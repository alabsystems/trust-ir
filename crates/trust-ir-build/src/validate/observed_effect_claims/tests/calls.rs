// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn direct_slot_precedes_earlier_duplicate_but_fallback_uses_first_matching_row() {
    let mut module = Module::new("duplicates");
    module.functions = vec![
        callee(1, "earlier-impure", false, false),
        callee(1, "slot-pure", true, false),
    ];
    let f = function(vec![node(
        Inst::Call {
            callee: FuncId::new(1),
            args: vec![],
        },
        &[],
    )]);
    assert!(parity(&f, Some(&module)).is_empty());
    module.functions = vec![
        callee(9, "first-impure", false, false),
        callee(9, "later-pure", true, false),
    ];
    let f = function(vec![node(
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        },
        &[],
    )]);
    let errors = parity(&f, Some(&module));
    assert_eq!(errors.len(), 1);
    assert_eq!(
        text(&errors[0]),
        "call @first-impure (the callee does not carry readnone)"
    );
    module.functions.swap(0, 1);
    assert!(parity(&f, Some(&module)).is_empty());
}
#[test]
fn every_direct_call_edge_respects_exact_callee_attribute_precedence() {
    let calls = [
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(9),
            args: vec![],
        },
        Inst::Invoke {
            callee: FuncId::new(9),
            args: vec![],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
        },
        Inst::SeqMap {
            ty: Ty::Sequence(TyId::new(0)),
            seq: v(1),
            fwd: FuncId::new(9),
        },
    ];
    for instruction in calls {
        for (readnone, readonly) in [(false, false), (true, false), (false, true), (true, true)] {
            let mut module = Module::new("call-attributes");
            module
                .functions
                .push(callee(9, "callee", readnone, readonly));
            let mut f = function(vec![node(instruction.clone(), &[])]);
            assert_eq!(parity(&f, Some(&module)).is_empty(), readnone);
            f.attrs.readnone = false;
            f.attrs.readonly = true;
            assert_eq!(parity(&f, Some(&module)).is_empty(), readnone || readonly);
        }
    }
}
#[test]
fn unresolved_call_context_and_u32_endpoints_keep_exact_decimal_diagnostics() {
    let module = Module::new("missing");
    for id in [0, 9, u32::MAX] {
        let f = function(vec![node(
            Inst::Call {
                callee: FuncId::new(id),
                args: vec![],
            },
            &[],
        )]);
        assert_eq!(
            text(&parity(&f, None)[0]),
            format!(
                "call to function #{id} (a callee's attributes cannot be resolved without module context)"
            )
        );
        assert_eq!(
            text(&parity(&f, Some(&module))[0]),
            format!("call to function #{id} (the callee does not resolve)")
        );
    }
}
#[test]
fn drops_use_exact_module_unique_ambiguous_and_unresolved_type_resolution() {
    let ty = Ty::Tuple(vec![Ty::U32, Ty::Array(TyId::new(0), u64::MAX)]);
    let instructions = [
        Inst::Drop {
            ty: ty.clone(),
            ptr: v(1),
        },
        Inst::DropInvoke {
            ty: ty.clone(),
            ptr: v(1),
            normal_dest: BlockId::new(1),
            normal_args: vec![v(1)],
            unwind_dest: BlockId::new(2),
        },
    ];
    for instruction in instructions {
        let mnemonic = names::mnemonic(&instruction);
        let f = function(vec![node(instruction, &[])]);
        let mut module = Module::new("drops");
        module.functions.push(callee(9, "glue", true, false));
        module.drop_glue.push(DropGlueEntry {
            ty: ty.clone(),
            glue: FuncId::new(9),
        });
        assert!(parity(&f, Some(&module)).is_empty());
        assert_eq!(
            text(&parity(&f, None)[0]),
            format!(
                "{mnemonic} (an unresolved drop runs an unstated destructor (no drop_glue row))"
            )
        );
        for glue in [9, 10] {
            module.drop_glue.push(DropGlueEntry {
                ty: ty.clone(),
                glue: FuncId::new(glue),
            });
            assert_eq!(
                text(&parity(&f, Some(&module))[0]),
                format!(
                    "{mnemonic} (an unresolved drop runs an unstated destructor (no drop_glue row))"
                )
            );
            module.drop_glue.pop();
        }
        module.functions.clear();
        assert_eq!(
            text(&parity(&f, Some(&module))[0]),
            format!("{mnemonic} to function #9 (the callee does not resolve)")
        );
        module.drop_glue.clear();
        assert_eq!(parity(&f, Some(&module)).len(), 1);
    }
}
#[test]
fn drop_type_keys_keep_nominal_ids_distinct_and_retain_the_actual_borrowed_index() {
    let f = function(vec![node(
        Inst::Drop {
            ty: Ty::Array(TyId::new(7), 4),
            ptr: v(1),
        },
        &[],
    )]);
    let mut module = Module::new("exact-keys");
    module.types = vec![Ty::U32; 8];
    module.functions.push(callee(9, "glue", true, false));
    module.drop_glue.push(DropGlueEntry {
        ty: Ty::Array(TyId::new(0), 4),
        glue: FuncId::new(9),
    });
    assert_eq!(parity(&f, Some(&module)).len(), 1);
    module.drop_glue[0].ty = Ty::Array(TyId::new(7), 4);
    assert!(parity(&f, Some(&module)).is_empty());
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.run(&f, Some(&module), &mut work).unwrap();
    assert!(core::ptr::eq(
        state.drop_index.as_ref().unwrap().source_module(),
        &module
    ));
    state.retire_scratch(&mut work);
    assert!(state.drop_index.is_none());
    state.retire_errors(&mut work);
    assert!(empty(&state));
}
#[test]
fn actual_callee_and_function_unicode_names_are_copied_without_normalization_or_escape() {
    let name = "target\0λ🙂'\\".repeat(1000);
    let mut module = Module::new("name-custody");
    module.functions.push(callee(9, &name, false, false));
    let mut f = function(vec![node(
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        },
        &[],
    )]);
    f.name = "function\0λ🙂".repeat(1000);
    let errors = parity(&f, Some(&module));
    assert_eq!(
        text(&errors[0]),
        format!("call @{name} (the callee does not carry readnone)")
    );
    assert!(
        matches!(&errors[0],ValidationError::FuncAttrClaimViolated{function,..} if function==&f.name)
    );
}
