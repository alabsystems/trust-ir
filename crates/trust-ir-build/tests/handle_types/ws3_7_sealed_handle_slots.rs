// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS3.7 (F-047, memory half): SEALED handle slots.
//!
//! A `Nat` local spilled to a function-local stack slot —
//! `let slot = v; let r = &slot; *r` — validates, because the slot is
//! SEALED: its pointer (and every borrow of it) is used only by exact-typed
//! `Store`s, exact-typed `Load`s and the borrow instructions, and every load
//! is dominated by a store.
//!
//! The spill fixtures alias the slot through `Borrow` / `BorrowMut`, the
//! permission machine's spelling, so their functions are UNSTAMPED: they pin
//! the sealed-slot join for a non-Rust producer whose discipline that machine
//! is. A Rust producer spells `&slot` as the slot address itself (SPEC "A Rust
//! reference carries no permission instruction"), which the `direct` fixture
//! pins, and a function stamped `Producer::TRust` carries no permission
//! instruction at all. Everything else stays refused, each by a NAMED
//! reason: a load before any store (an uninitialized word would be a forged
//! handle), the slot pointer escaping into a call / `GEP` / cast / branch /
//! another store, a differently typed access (the `PtrToInt` leak through
//! memory), a volatile or misaligned access, a dynamic count, a slot type the
//! rule does not open, and a handle behind a `Ref` parameter (phase 2).
//!
//! Each negative is the positive module with ONE edit, and asserts that every
//! refusal is `InvalidHandleUse` and that one of them names the rule.

use trust_ir::inst::CastOp;
use trust_ir::ty::{EnumDef, EnumVariant, FieldDef, StructDef};
use trust_ir::value::{EnumId, StructId};
use trust_ir::{
    BodyGate, Endianness, FuncId, Inst, Module, Producer, StructPassingPolicy, TargetInfo,
    TupleLayoutDescriptor, Ty, ValueId,
};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    FunctionBuilder, HandleRuntimeDecls, ModuleBuilder, TRUSTED_HANDLE_RUNTIMES, validate_changed,
    validate_module, validate_module_for_codegen,
};

fn nat() -> Ty {
    Ty::handle("Nat", "trust_bignum::Nat")
}

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn gate() -> BodyGate {
    BodyGate::Gated {
        authority: "ws3.7".into(),
        evidence: None,
    }
}

/// What a body closure can reach: the pinned declarations and a local
/// `sink(p: ptr)` that a slot pointer can escape into.
struct Ctx<'d> {
    decls: &'d HandleRuntimeDecls,
    sink: FuncId,
}

/// The pinned `Nat` declarations, `sink(p: ptr) {}`, the module's type
/// tables from `pre`, and `spill_local(x: Nat) -> Nat { <body> }`, where
/// `body` returns the value the function returns.
fn spill_module(
    name: &str,
    pre: impl FnOnce(&mut Module),
    body: impl FnOnce(&mut FunctionBuilder<'_>, ValueId, &Ctx<'_>) -> ValueId,
) -> Module {
    // Unstamped: the bodies alias the slot through the permission machine (see
    // the module docs), which no Rust producer emits.
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    let decls = mb
        .declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
        .expect("pinned runtime declares");
    let sink_sig = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let sink = {
        let mut fb = mb.function("sink", sink_sig);
        let entry = fb.create_block();
        let _ = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.set_body_gate(gate());
        fb.build()
    };
    let sig = mb.add_func_type(vec![nat()], vec![nat()]);
    let mut fb = mb.function("spill_local", sig);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, nat());
    fb.switch_to_block(entry);
    let ctx = Ctx {
        decls: &decls,
        sink,
    };
    let out = body(&mut fb, x, &ctx);
    fb.ret(vec![out]);
    fb.set_body_gate(gate());
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    pre(&mut module);
    module
}

/// `b5_12`'s `spill_local`: `let slot = x; let r = &slot; *r`.
fn spill(fb: &mut FunctionBuilder<'_>, x: ValueId) -> ValueId {
    let slot = fb.alloca(nat());
    fb.store(nat(), slot, x);
    let r = fb.borrow(slot);
    let out = fb.load(nat(), r);
    fb.end_borrow(r);
    out
}

fn spill_function(module: &Module) -> FuncId {
    module
        .functions
        .iter()
        .find(|f| f.name == "spill_local")
        .expect("spill_local")
        .id
}

/// Every refusal is `InvalidHandleUse`, and one of them names `needle`.
fn refused_naming(errors: &[ValidationError], needle: &str) -> bool {
    !errors.is_empty()
        && errors
            .iter()
            .all(|e| matches!(e, ValidationError::InvalidHandleUse { .. }))
        && errors.iter().any(
            |e| matches!(e, ValidationError::InvalidHandleUse { detail, .. } if detail.contains(needle)),
        )
}

const SEALED: &str = "a handle slot is sealed: it may only be loaded and stored at its exact type \
                      and never escapes";
const UNINITIALIZED: &str = "load of a handle slot not dominated by a store";
const NOT_A_SLOT: &str = "goes through a pointer that is not a sealed handle slot";

// ───────────────────────────── POSITIVE ─────────────────────────────

/// The roadmap's positive fixture: `b5_12`'s `spill_local` at `Nat`.
#[test]
fn ws3_7_a_spilled_nat_local_validates() {
    let module = spill_module("ws3_7_spill", |_| {}, |fb, x, _| spill(fb, x));
    assert_eq!(validate_module(&module), vec![]);
    // The incremental lane agrees on the changed function.
    assert_eq!(
        validate_changed(&module, &[spill_function(&module)]),
        vec![]
    );
    // The slot needs no borrow: a store then a load through the slot itself.
    // This is the Rust producers' spelling of the spill, stamped as theirs.
    let direct = spill_module(
        "ws3_7_direct",
        |module| {
            for function in &mut module.functions {
                function.producer = Some(Producer::TRust);
            }
        },
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            fb.load(nat(), slot)
        },
    );
    assert_eq!(validate_module(&direct), vec![]);
    // A later exact-typed store overwrites; reads after either are initialized.
    let restored = spill_module(
        "ws3_7_restore",
        |_| {},
        |fb, x, ctx| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let first = fb.load(nat(), slot);
            let doubled = fb.call(ctx.decls.entry("add").unwrap(), vec![first, first]);
            let r = fb.borrow_mut(slot);
            fb.store(nat(), r, doubled);
            fb.end_borrow(r);
            fb.load(nat(), slot)
        },
    );
    assert_eq!(validate_module(&restored), vec![]);
}

/// The codegen lane is the structural validator plus lowerability: it admits
/// exactly what `validate_module` admits here, and the SAME refusals hold.
/// (trust-cg itself keeps refusing handle memory until it lowers sealed slots
/// — WS7; its admitted set is a strict subset, so this is fail closed.)
#[test]
fn ws3_7_the_codegen_lane_agrees() {
    let module = spill_module("ws3_7_codegen", |_| {}, |fb, x, _| spill(fb, x));
    assert_eq!(validate_module_for_codegen(&module), vec![]);
    let unstored = spill_module(
        "ws3_7_codegen_unstored",
        |_| {},
        |fb, _, _| {
            let slot = fb.alloca(nat());
            fb.load(nat(), slot)
        },
    );
    assert!(refused_naming(
        &validate_module_for_codegen(&unstored),
        UNINITIALIZED
    ));
}

/// A handle-bearing struct and tuple are sealable slot types too (the WS3.6
/// register carriers): build, spill, reload, project. A slot needs a memory
/// image, and a struct has one only through its declared `size` / `align` /
/// field offsets, a tuple only through a declared v42 tuple layout — so each
/// carrier's slot WITHOUT one is refused ("has no computable layout"): fail
/// closed, never guessed. (REVIEW: the struct case used to declare no layout
/// and assert that it validated; that assertion never ran, because the test
/// did not compile — and it was false.)
#[test]
fn ws3_7_a_handle_bearing_struct_or_tuple_slot_validates() {
    let acct = Ty::Struct(StructId::new(0));
    let pair = Ty::Tuple(vec![Ty::U64, nat()]);
    let tables = |declare_layouts: bool| {
        let pair = pair.clone();
        move |module: &mut Module| {
            module.add_struct(StructDef {
                id: StructId::new(0),
                name: "Acct".into(),
                fields: vec![FieldDef {
                    name: "bal".into(),
                    ty: nat(),
                    offset: declare_layouts.then_some(0),
                }],
                size: declare_layouts.then_some(8),
                align: declare_layouts.then_some(8),
                repr: trust_ir::StructRepr::C,
                origin: None,
            });
            if declare_layouts {
                let tuple_type = module
                    .add_type(pair)
                    .expect("Module::add_type: test fixture");
                module.tuple_layouts.push(TupleLayoutDescriptor {
                    tuple_type,
                    size: 16,
                    align: 8,
                    field_offsets: vec![0, 8],
                });
            }
        }
    };
    // Build the carrier, spill it, reload it and project the handle lane
    // (`lane_read`: read the handle lane straight out of the slot instead).
    let carrier_module = |carrier: Ty, declare_layouts: bool, lane_read: bool| {
        let lane = u32::from(matches!(carrier, Ty::Tuple(_)));
        spill_module("ws3_7_carrier", tables(declare_layouts), move |fb, x, _| {
            let fields = if lane == 0 {
                vec![x]
            } else {
                vec![fb.iconst(Ty::U64, 7), x]
            };
            let value = fb.make_aggregate(carrier.clone(), fields);
            let slot = fb.alloca(carrier.clone());
            fb.store(carrier.clone(), slot, value);
            if lane_read {
                fb.load(nat(), slot)
            } else {
                let back = fb.load(carrier.clone(), slot);
                fb.extract_field(nat(), back, lane)
            }
        })
    };
    for carrier in [acct, pair.clone()] {
        let module = carrier_module(carrier.clone(), true, false);
        assert_eq!(validate_module(&module), vec![], "{carrier}");

        // Twin: the handle lane read straight out of the slot at `Nat` — a
        // load at a type other than the slot's own.
        let errors = validate_module(&carrier_module(carrier.clone(), true, true));
        assert!(
            refused_naming(
                &errors,
                &format!("reads it at `{}`, not at the slot's own type", nat())
            ),
            "{carrier}: {errors:?}"
        );

        // Twin: the same carrier with no declared layout has no memory image
        // to seal.
        let errors = validate_module(&carrier_module(carrier.clone(), false, false));
        assert!(
            refused_naming(&errors, "has no computable layout"),
            "{carrier}: {errors:?}"
        );
    }
}

// ─────────────────────── NEGATIVE TWINS (roadmap) ───────────────────────

/// Twin 1: the same module with the `Load` before any `Store`.
#[test]
fn ws3_7_a_load_before_any_store_is_refused() {
    let module = spill_module(
        "ws3_7_load_first",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            let out = fb.load(nat(), slot);
            fb.store(nat(), slot, x);
            out
        },
    );
    let errors = validate_module(&module);
    assert!(refused_naming(&errors, UNINITIALIZED), "{errors:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");

    // No store at all.
    let never = spill_module(
        "ws3_7_never_stored",
        |_| {},
        |fb, _, _| {
            let slot = fb.alloca(nat());
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&never);
    assert!(refused_naming(&errors, UNINITIALIZED), "{errors:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");
}

/// Twin 2: the slot pointer passed to a call.
#[test]
fn ws3_7_the_slot_pointer_passed_to_a_call_is_refused() {
    let module = spill_module(
        "ws3_7_call",
        |_| {},
        |fb, x, ctx| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            fb.call_void(ctx.sink, vec![slot]);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&module);
    assert!(refused_naming(&errors, SEALED), "{errors:?}");
    assert!(refused_naming(&errors, "escapes into `Call`"), "{errors:?}");
}

/// Twin 3: `GEP` on the slot.
#[test]
fn ws3_7_a_gep_on_the_slot_is_refused() {
    let module = spill_module(
        "ws3_7_gep",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let _ = fb.gep_byte_offset(slot, 0);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&module);
    assert!(refused_naming(&errors, "escapes into `GEP`"), "{errors:?}");
}

// ─────────────────────── MUTATIONS / ADVERSARIAL ───────────────────────

/// (a) `Store U64` into the slot then `Load H`: the store type is not the
/// slot type, so the slot is unsealed and the load reads an unsealed slot.
#[test]
fn ws3_7_a_u64_store_then_a_nat_load_is_refused() {
    let module = spill_module(
        "ws3_7_u64_store",
        |_| {},
        |fb, _, _| {
            let slot = fb.alloca(nat());
            let seven = fb.iconst(Ty::U64, 7);
            fb.store(Ty::U64, slot, seven);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&module);
    assert!(
        refused_naming(&errors, &format!("writes it at `{}`", Ty::U64)),
        "{errors:?}"
    );
    // The mirror: a `Nat` slot read back as `U64` is the PtrToInt leak
    // through memory.
    let leak = spill_module(
        "ws3_7_u64_load",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let _ = fb.load(Ty::U64, slot);
            x
        },
    );
    let errors = validate_module(&leak);
    assert!(
        refused_naming(&errors, &format!("reads it at `{}`", Ty::U64)),
        "{errors:?}"
    );
}

/// (b) A store on only one arm of a diamond does not initialize the join —
/// conservative by design. Storing on BOTH arms is refused too (neither store
/// dominates the join); the producer's fix is to store right after the
/// `Alloca`, which validates.
#[test]
fn ws3_7_a_store_on_one_arm_of_a_diamond_does_not_initialize_the_join() {
    let diamond = |name: &str, then_store: bool, else_store: bool| {
        spill_module(
            name,
            |_| {},
            move |fb, x, ctx| {
                let slot = fb.alloca(nat());
                let z = fb.call(ctx.decls.entry("is_zero").unwrap(), vec![x]);
                let then_b = fb.create_block();
                let else_b = fb.create_block();
                let join = fb.create_block();
                fb.condbr(z, then_b, vec![], else_b, vec![]);
                fb.switch_to_block(then_b);
                if then_store {
                    fb.store(nat(), slot, x);
                }
                fb.br(join, vec![]);
                fb.switch_to_block(else_b);
                if else_store {
                    fb.store(nat(), slot, x);
                }
                fb.br(join, vec![]);
                fb.switch_to_block(join);
                fb.load(nat(), slot)
            },
        )
    };
    for (then_store, else_store) in [(true, false), (false, true), (true, true)] {
        let errors = validate_module(&diamond("ws3_7_diamond", then_store, else_store));
        assert!(
            refused_naming(&errors, UNINITIALIZED),
            "then={then_store} else={else_store}: {errors:?}"
        );
    }
    // The control: the store dominates the branch.
    let dominated = spill_module(
        "ws3_7_diamond_ok",
        |_| {},
        |fb, x, ctx| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let z = fb.call(ctx.decls.entry("is_zero").unwrap(), vec![x]);
            let then_b = fb.create_block();
            let else_b = fb.create_block();
            let join = fb.create_block();
            fb.condbr(z, then_b, vec![], else_b, vec![]);
            fb.switch_to_block(then_b);
            fb.br(join, vec![]);
            fb.switch_to_block(else_b);
            fb.br(join, vec![]);
            fb.switch_to_block(join);
            fb.load(nat(), slot)
        },
    );
    assert_eq!(validate_module(&dominated), vec![]);
}

/// (c) `Borrow` the slot, `Cast PtrToInt` the borrow: the borrow IS the slot,
/// so its escape unseals it.
#[test]
fn ws3_7_ptr_to_int_of_a_borrow_of_the_slot_is_refused() {
    let module = spill_module(
        "ws3_7_ptrtoint",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let r = fb.borrow(slot);
            let _ = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, r);
            let out = fb.load(nat(), r);
            fb.end_borrow(r);
            out
        },
    );
    let errors = validate_module(&module);
    assert!(refused_naming(&errors, "escapes into `Cast`"), "{errors:?}");
}

/// The other escapes the rule names: a branch argument, a `Store` of the
/// pointer AS A VALUE, a `Copy` of it, and a borrow of a borrow that escapes.
#[test]
fn ws3_7_every_other_escape_is_refused() {
    let branch = spill_module(
        "ws3_7_branch",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let next = fb.create_block();
            let p = fb.add_block_param(next, Ty::Ptr);
            fb.br(next, vec![slot]);
            fb.switch_to_block(next);
            fb.load(nat(), p)
        },
    );
    let errors = validate_module(&branch);
    assert!(refused_naming(&errors, "escapes into `Br`"), "{errors:?}");
    // ...and the load through the block parameter is not a slot access.
    assert!(refused_naming(&errors, NOT_A_SLOT), "{errors:?}");

    let stored = spill_module(
        "ws3_7_stored_pointer",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let cell = fb.alloca(Ty::Ptr);
            fb.store(Ty::Ptr, cell, slot);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&stored);
    assert!(refused_naming(&errors, "stored AS A VALUE"), "{errors:?}");

    let copied = spill_module(
        "ws3_7_copied_pointer",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let _ = fb.copy(Ty::Ptr, slot);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&copied);
    assert!(refused_naming(&errors, "escapes into `Copy`"), "{errors:?}");

    let nested = spill_module(
        "ws3_7_nested_borrow",
        |_| {},
        |fb, x, ctx| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let r = fb.borrow(slot);
            let rr = fb.borrow(r);
            fb.call_void(ctx.sink, vec![rr]);
            fb.load(nat(), rr)
        },
    );
    let errors = validate_module(&nested);
    assert!(refused_naming(&errors, "escapes into `Call`"), "{errors:?}");
}

/// Volatile and non-natural `align` accesses, an under-aligned slot, and a
/// dynamic count are refused; an over-aligned slot is still naturally
/// aligned and validates.
#[test]
fn ws3_7_only_plain_naturally_aligned_single_slots_are_sealed() {
    let volatile = spill_module(
        "ws3_7_volatile",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            fb.load_volatile(nat(), slot)
        },
    );
    assert!(refused_naming(
        &validate_module(&volatile),
        "may not be volatile"
    ));
    let volatile_store = spill_module(
        "ws3_7_volatile_store",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store_volatile(nat(), slot, x);
            fb.load(nat(), slot)
        },
    );
    assert!(refused_naming(
        &validate_module(&volatile_store),
        "may not be volatile"
    ));

    let misaligned = spill_module(
        "ws3_7_misaligned",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            fb.load_aligned(nat(), slot, 4)
        },
    );
    assert!(refused_naming(
        &validate_module(&misaligned),
        "not the type's natural alignment"
    ));
    // The natural alignment spelled explicitly is the same access.
    let natural = spill_module(
        "ws3_7_natural",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store_aligned(nat(), slot, x, 8);
            fb.load_aligned(nat(), slot, 8)
        },
    );
    assert_eq!(validate_module(&natural), vec![]);

    let under = spill_module(
        "ws3_7_under_aligned",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca_aligned(nat(), 4);
            fb.store(nat(), slot, x);
            fb.load(nat(), slot)
        },
    );
    assert!(refused_naming(
        &validate_module(&under),
        "at least the natural alignment"
    ));
    let over = spill_module(
        "ws3_7_over_aligned",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca_aligned(nat(), 16);
            fb.store(nat(), slot, x);
            fb.load(nat(), slot)
        },
    );
    assert_eq!(validate_module(&over), vec![]);

    // A dynamic count is an array of handles.
    let mut counted = spill_module(
        "ws3_7_counted",
        |_| {},
        |fb, x, _| {
            let _count = fb.iconst(Ty::U64, 2);
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            fb.load(nat(), slot)
        },
    );
    let spill_id = spill_function(&counted);
    let func = counted
        .functions
        .iter_mut()
        .find(|f| f.id == spill_id)
        .unwrap();
    let count_value = func.blocks[0].body[0].results[0];
    let Inst::Alloca { count, .. } = &mut func.blocks[0].body[1].inst else {
        panic!("the alloca");
    };
    *count = Some(count_value);
    assert!(refused_naming(&validate_module(&counted), "dynamic count"));
}

/// A slot of a type the rule does not open — an enum carrying a handle — is
/// refused by name, even when it is used exactly like a sealed slot.
#[test]
fn ws3_7_an_enum_slot_type_is_not_sealable() {
    let lvl = Ty::Enum(EnumId::new(0));
    let add_lvl = |module: &mut Module| {
        module.add_enum(EnumDef::new(
            EnumId::new(0),
            "Lvl",
            vec![
                EnumVariant {
                    name: "zero".into(),
                    fields: vec![],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "param".into(),
                    fields: vec![nat()],
                    field_names: vec!["n".into()],
                },
            ],
        ));
    };
    let l = lvl.clone();
    let module = spill_module("ws3_7_enum_slot", add_lvl, move |fb, x, _| {
        let value = fb.make_enum_variant(l.clone(), 1, vec![x]);
        let slot = fb.alloca(l.clone());
        fb.store(l.clone(), slot, value);
        let _ = fb.load(l.clone(), slot);
        x
    });
    let errors = validate_module(&module);
    assert!(
        refused_naming(&errors, "is not a sealable slot type"),
        "{errors:?}"
    );
}

/// Initialization is PER SLOT: a store into one slot does not initialize
/// another.
#[test]
fn ws3_7_a_store_into_one_slot_does_not_initialize_another() {
    let module = spill_module(
        "ws3_7_two_slots",
        |_| {},
        |fb, x, _| {
            let a = fb.alloca(nat());
            let b = fb.alloca(nat());
            fb.store(nat(), a, x);
            let _ = fb.load(nat(), a);
            fb.load(nat(), b)
        },
    );
    let errors = validate_module(&module);
    assert!(refused_naming(&errors, UNINITIALIZED), "{errors:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");
}

/// A handle behind a `Ref` / `RefMut` PARAMETER is phase 2 (DG-46, gated on
/// WS5 F-094): a load or store through any pointer that is not a sealed slot
/// is refused, never admitted because the pointee type says `Nat`.
#[test]
fn ws3_7_a_handle_behind_a_ref_parameter_is_phase_2() {
    let mut mb = ModuleBuilder::new_with_target_info("ws3_7_ref_param", target());
    mb.set_default_producer(Producer::TRust);
    mb.declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
        .expect("pinned runtime declares");
    let sig = mb.add_func_type(vec![Ty::Ref(Box::new(nat()))], vec![nat()]);
    let mut fb = mb.function("read_ref", sig);
    let entry = fb.create_block();
    let r = fb.add_block_param(entry, Ty::Ref(Box::new(nat())));
    fb.switch_to_block(entry);
    let v = fb.load(nat(), r);
    fb.ret(vec![v]);
    fb.set_body_gate(gate());
    fb.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(refused_naming(&errors, NOT_A_SLOT), "{errors:?}");
    assert_eq!(errors.len(), 1, "{errors:?}");
}

/// Instance soundness does not lean on the deep SSA pass. `validate_changed`
/// FILTERS that pass (here: to no function at all), but the handle rule runs
/// on every function, so a load through a borrow used BEFORE the borrow's
/// definition is refused by the slot rule itself — under the filter as well
/// as in the full validator.
#[test]
fn ws3_7_a_slot_pointer_used_before_its_definition_is_refused_even_when_filtered() {
    let mut module = spill_module("ws3_7_use_before_def", |_| {}, |fb, x, _| spill(fb, x));
    // `spill` emits [alloca, store, borrow r, load r, end_borrow r, ret];
    // move the borrow below the load.
    let spill_id = spill_function(&module);
    let func = module
        .functions
        .iter_mut()
        .find(|f| f.id == spill_id)
        .unwrap();
    assert!(matches!(func.blocks[0].body[2].inst, Inst::Borrow { .. }));
    assert!(matches!(func.blocks[0].body[3].inst, Inst::Load { .. }));
    func.blocks[0].body.swap(2, 3);

    let filtered = validate_changed(&module, &[]);
    assert!(
        refused_naming(&filtered, "where its definition does not dominate the use"),
        "{filtered:?}"
    );
    let full = validate_module(&module);
    assert!(
        full.iter().any(|e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. }
                if detail.contains("where its definition does not dominate the use")
        )),
        "{full:?}"
    );
}

/// `HeapAlloc` and `Dealloc` of a handle, and a handle-typed global, stay
/// refused: the sealed slot is the ONLY memory a handle may occupy.
#[test]
fn ws3_7_heap_and_global_storage_stay_refused() {
    let heap = spill_module(
        "ws3_7_heap",
        |_| {},
        |fb, x, _| {
            let p = fb.heap_alloc(nat(), None, None, trust_ir::inst::AllocOrigin::RustHeap);
            fb.store(nat(), p, x);
            fb.load(nat(), p)
        },
    );
    let errors = validate_module(&heap);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. } if detail.contains("`HeapAlloc`")
        )),
        "{errors:?}"
    );
    assert!(refused_naming(&errors, NOT_A_SLOT), "{errors:?}");

    let mut global = spill_module("ws3_7_global", |_| {}, |fb, x, _| spill(fb, x));
    global.globals.push(trust_ir::Global {
        name: "NAT_CACHE".into(),
        ty: nat(),
        mutable: true,
        initializer: None,
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    let errors = validate_module(&global);
    assert!(
        refused_naming(&errors, "globals declare machine storage"),
        "{errors:?}"
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
}

// ─────────────────────────── REVIEW (adversarial) ───────────────────────────

/// `spill_local`, mutably, for the post-build mutations below.
fn spill_function_mut(module: &mut Module) -> &mut trust_ir::Function {
    let id = spill_function(module);
    module
        .functions
        .iter_mut()
        .find(|f| f.id == id)
        .expect("spill_local")
}

/// REVIEW: `MemCopy` and `MemSet` carry NO type, so the handle arm never
/// fires on them — only the slot's own use scan sees them. Each is refused by
/// name: the handle's word copied OUT into a `U64` cell (the `PtrToInt` leak
/// with no cast), a `U64` cell's bytes copied IN over an initialized handle
/// (the forge a dominating exact-typed store would otherwise hide), and a
/// `MemSet` over an initialized slot (the same forge from a literal byte).
#[test]
fn ws3_7_review_memcopy_and_memset_cannot_move_bytes_through_the_slot() {
    let copied_out = spill_module(
        "ws3_7_memcopy_out",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let cell = fb.alloca(Ty::U64);
            let bytes = fb.iconst(Ty::Usize, 8);
            fb.memcopy(cell, slot, bytes, false);
            let _ = fb.load(Ty::U64, cell);
            x
        },
    );
    let errors = validate_module(&copied_out);
    assert!(refused_naming(&errors, SEALED), "{errors:?}");
    assert!(
        refused_naming(&errors, "escapes into `MemCopy`"),
        "{errors:?}"
    );

    let copied_in = spill_module(
        "ws3_7_memcopy_in",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let cell = fb.alloca(Ty::U64);
            let word = fb.iconst(Ty::U64, 0x41);
            fb.store(Ty::U64, cell, word);
            let bytes = fb.iconst(Ty::Usize, 8);
            fb.memcopy(slot, cell, bytes, true);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&copied_in);
    assert!(
        refused_naming(&errors, "escapes into `MemCopy`"),
        "{errors:?}"
    );
    // The dominating store does not rescue the load: the slot is unsealed.
    assert!(refused_naming(&errors, "which is not sealed"), "{errors:?}");

    let overwritten = spill_module(
        "ws3_7_memset",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let byte = fb.iconst(Ty::U8, 0x41);
            let bytes = fb.iconst(Ty::Usize, 8);
            fb.memset(slot, byte, bytes);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&overwritten);
    assert!(
        refused_naming(&errors, "escapes into `MemSet`"),
        "{errors:?}"
    );
    assert!(refused_naming(&errors, "which is not sealed"), "{errors:?}");
}

/// REVIEW: the typeless escapes the roadmap lists but the twins above did not
/// pin — each carries no handle type, so only the use scan refuses it: a
/// `Select` of the pointer, an `AtomicLoad` of the handle's word at `U64`, a
/// `Drop` of the slot at `U64`, and the slot pointer RETURNED to the caller.
#[test]
fn ws3_7_review_typeless_escapes_are_refused_by_name() {
    let selected = spill_module(
        "ws3_7_select",
        |_| {},
        |fb, x, ctx| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let z = fb.call(ctx.decls.entry("is_zero").unwrap(), vec![x]);
            let _ = fb.select(Ty::Ptr, z, slot, slot);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&selected);
    assert!(
        refused_naming(&errors, "escapes into `Select`"),
        "{errors:?}"
    );

    let atomic = spill_module(
        "ws3_7_atomic",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let _ = fb.atomic_load(Ty::U64, slot, trust_ir::inst::Ordering::SeqCst);
            fb.load(nat(), slot)
        },
    );
    let errors = validate_module(&atomic);
    assert!(
        refused_naming(&errors, "escapes into `AtomicLoad`"),
        "{errors:?}"
    );

    // Insert a `Drop` after the store. It drops the slot's own type: a drop
    // of a trivially droppable type (the `U64` this once used) is now its own
    // refusal (`NonCanonicalDrop`, amendment D §20 rule 5a), and the subject
    // here is the escape alone.
    let mut dropped = spill_module(
        "ws3_7_drop",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            fb.load(nat(), slot)
        },
    );
    let body = &mut spill_function_mut(&mut dropped).blocks[0].body;
    let slot = body[0].results[0];
    body.insert(
        2,
        trust_ir::InstrNode::new(Inst::Drop {
            ty: nat(),
            ptr: slot,
        }),
    );
    let errors = validate_module(&dropped);
    assert!(refused_naming(&errors, "escapes into `Drop`"), "{errors:?}");

    // The slot pointer handed back to the caller.
    let mut mb = ModuleBuilder::new_with_target_info("ws3_7_returned", target());
    mb.set_default_producer(Producer::TRust);
    mb.declare_handle_runtime(&TRUSTED_HANDLE_RUNTIMES[0])
        .expect("pinned runtime declares");
    let sig = mb.add_func_type(vec![nat()], vec![Ty::Ptr]);
    let mut fb = mb.function("leak_slot", sig);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, nat());
    fb.switch_to_block(entry);
    let slot = fb.alloca(nat());
    fb.store(nat(), slot, x);
    fb.ret(vec![slot]);
    fb.set_body_gate(gate());
    fb.build();
    let errors = validate_module(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(
        refused_naming(&errors, "escapes into `Return`"),
        "{errors:?}"
    );
}

/// REVIEW: the slot's store must itself be exact. A `Store` AT the slot type
/// whose value is not of that type is refused by the handle rule's own value
/// check — which is what stands when the deep pass (whose generic store-type
/// check would also fire) is filtered off under `validate_changed`.
#[test]
fn ws3_7_review_a_store_at_the_slot_type_needs_a_value_of_that_type() {
    let mut module = spill_module(
        "ws3_7_store_value_type",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            let _seven = fb.iconst(Ty::U64, 7);
            fb.store(nat(), slot, x);
            fb.load(nat(), slot)
        },
    );
    // Store the `U64` constant at `Nat` instead of `x`.
    let body = &mut spill_function_mut(&mut module).blocks[0].body;
    let seven = body[1].results[0];
    let Inst::Store { value, .. } = &mut body[2].inst else {
        panic!("the store");
    };
    *value = seven;

    const NEEDLE: &str = "needs a value of exactly that type";
    let filtered = validate_changed(&module, &[]);
    assert!(refused_naming(&filtered, NEEDLE), "{filtered:?}");
    let full = validate_module(&module);
    assert!(
        full.iter().any(|e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. } if detail.contains(NEEDLE)
        )),
        "{full:?}"
    );
}

/// REVIEW: a handle stored into a slot that is NOT a handle slot — a `U64`
/// or `Ptr` cell in a function that also holds a sealed slot, so the analysis
/// exists — is refused at the store: the cell was never a handle slot, and
/// reading it back at `U64` would be the leak.
#[test]
fn ws3_7_review_a_handle_stored_into_a_non_handle_cell_is_refused() {
    for cell_ty in [Ty::U64, Ty::Ptr] {
        let module = spill_module(
            "ws3_7_foreign_cell",
            |_| {},
            move |fb, x, _| {
                let out = spill(fb, x);
                let cell = fb.alloca(cell_ty.clone());
                fb.store(nat(), cell, x);
                let _ = fb.load(cell_ty.clone(), cell);
                out
            },
        );
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::InvalidHandleUse { detail, .. }
                    if detail.starts_with(&format!("`Store` at `{}` goes through a pointer", nat()))
            )),
            "{errors:?}"
        );
    }
}

/// REVIEW: a slot pointer with more than one definition is refused by the
/// slot rule itself — the filtered lane has no deep SSA pass to catch it.
/// The attack: after the store, redefine the slot's ValueId as an
/// `IntToPtr` of a guessed address, so the "slot" load reads that address.
#[test]
fn ws3_7_review_a_redefined_slot_pointer_is_refused_even_when_filtered() {
    let mut module = spill_module(
        "ws3_7_redefined",
        |_| {},
        |fb, x, _| {
            let slot = fb.alloca(nat());
            fb.store(nat(), slot, x);
            let guess = fb.iconst(Ty::U64, 4096);
            let forged = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, guess);
            fb.load(nat(), forged)
        },
    );
    // [alloca, store, iconst, cast, load, ret]: the cast now defines the
    // slot's own ValueId, and the load reads through it.
    let body = &mut spill_function_mut(&mut module).blocks[0].body;
    let slot = body[0].results[0];
    assert!(matches!(body[3].inst, Inst::Cast { .. }));
    body[3].results[0] = slot;
    let Inst::Load { ptr, .. } = &mut body[4].inst else {
        panic!("the load");
    };
    *ptr = slot;

    const NEEDLE: &str = "is defined more than once";
    let filtered = validate_changed(&module, &[]);
    assert!(
        filtered.iter().any(|e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. } if detail.contains(NEEDLE)
        )),
        "{filtered:?}"
    );
    let full = validate_module(&module);
    assert!(
        full.iter().any(|e| matches!(
            e,
            ValidationError::InvalidHandleUse { detail, .. } if detail.contains(NEEDLE)
        )),
        "{full:?}"
    );
}

/// REVIEW: an `Alloca` of a handle with no single result defines no slot
/// pointer; with zero results and with two it is refused by name.
#[test]
fn ws3_7_review_an_alloca_without_a_single_result_is_refused() {
    for extra in [None, Some(ValueId::new(9_999))] {
        let mut module = spill_module("ws3_7_results", |_| {}, |fb, x, _| spill(fb, x));
        let body = &mut spill_function_mut(&mut module).blocks[0].body;
        assert!(matches!(body[0].inst, Inst::Alloca { .. }));
        match extra {
            None => body[0].results.clear(),
            Some(value) => body[0].results.push(value),
        }
        let errors = validate_module(&module);
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::InvalidHandleUse { detail, .. }
                    if detail.contains("this allocation defines no single slot pointer")
            )),
            "{extra:?}: {errors:?}"
        );
    }
}

/// REVIEW: loops. An `Alloca` in a loop header makes a FRESH slot each
/// iteration: a store in the latch (the previous iteration's slot) does not
/// initialize a read in the header or at the exit. The control stores right
/// after the `Alloca` and validates.
#[test]
fn ws3_7_review_a_latch_store_does_not_initialize_the_next_iteration() {
    // entry -> header; header: slot = alloca; [store]; [load]; condbr ->
    // exit | latch; latch: [store]; br header; exit: load.
    let looped = |name: &str, store_in_header: bool, load_in_header: bool| {
        spill_module(
            name,
            |_| {},
            move |fb, x, ctx| {
                let header = fb.create_block();
                let latch = fb.create_block();
                let exit = fb.create_block();
                fb.br(header, vec![]);
                fb.switch_to_block(header);
                let slot = fb.alloca(nat());
                if store_in_header {
                    fb.store(nat(), slot, x);
                }
                if load_in_header {
                    let _ = fb.load(nat(), slot);
                }
                let z = fb.call(ctx.decls.entry("is_zero").unwrap(), vec![x]);
                fb.condbr(z, exit, vec![], latch, vec![]);
                fb.switch_to_block(latch);
                fb.store(nat(), slot, x);
                fb.br(header, vec![]);
                fb.switch_to_block(exit);
                fb.load(nat(), slot)
            },
        )
    };
    for load_in_header in [false, true] {
        let errors = validate_module(&looped("ws3_7_loop", false, load_in_header));
        assert!(
            refused_naming(&errors, UNINITIALIZED),
            "load_in_header={load_in_header}: {errors:?}"
        );
    }
    assert_eq!(
        validate_module(&looped("ws3_7_loop_ok", true, true)),
        vec![]
    );
}

/// REVIEW: an unwind edge is a real predecessor. A store only on an
/// `Invoke`'s NORMAL continuation does not initialize a join the landing pad
/// also reaches; the control stores before the `Invoke` and validates.
#[test]
fn ws3_7_review_a_normal_edge_store_does_not_initialize_the_unwind_join() {
    let invoked = |name: &str, store_before: bool| {
        spill_module(
            name,
            |_| {},
            move |fb, x, ctx| {
                let slot = fb.alloca(nat());
                if store_before {
                    fb.store(nat(), slot, x);
                }
                let normal = fb.create_block();
                let pad = fb.create_block();
                let join = fb.create_block();
                let _ = fb.invoke(
                    ctx.decls.entry("is_zero").unwrap(),
                    vec![x],
                    normal,
                    vec![],
                    pad,
                );
                fb.switch_to_block(normal);
                if !store_before {
                    fb.store(nat(), slot, x);
                }
                fb.br(join, vec![]);
                fb.switch_to_block(pad);
                let _ = fb.landingpad(true, vec![]);
                fb.br(join, vec![]);
                fb.switch_to_block(join);
                fb.load(nat(), slot)
            },
        )
    };
    let errors = validate_module(&invoked("ws3_7_invoke", false));
    assert!(refused_naming(&errors, UNINITIALIZED), "{errors:?}");
    assert_eq!(validate_module(&invoked("ws3_7_invoke_ok", true)), vec![]);
}
