// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual counterexamples retained as independent interpreter/validator controls.
use super::*;
use trust_ir::interpret::{
    ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
};
use trust_ir_build::validate::validate_function_binding_frames_observed;

struct Admit;
impl ExecutionObserver for Admit {
    type Refusal = core::convert::Infallible;
    fn admit(&mut self, _: ExecutionProgress) -> Result<(), Self::Refusal> {
        Ok(())
    }
}
fn checked(text: &str) -> (Module, Vec<ValidationError>) {
    let module = trust_ir::parser::parse_module(text).expect("fixed counterexample parses");
    let function = &module.functions[0];
    let mut observer = Admit;
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let observed = validate_function_binding_frames_observed(
        function,
        &mut session,
        ExecutionSite::Entry(function.id),
    )
    .expect("unbounded observation completes");
    let all = trust_ir_build::validate_module(&module);
    assert!(
        observed.iter().all(|error| all.contains(error)),
        "observed diagnostics also reach module validation"
    );
    (module, all)
}
fn execute(module: &Module, argument: InterpretValue) -> InterpretResult<i128> {
    let outcome =
        Interpreter::with_module(module).execute_func(module.functions[0].id, [argument])?;
    assert_eq!(outcome.host_calls, 0);
    assert_eq!(outcome.returns.len(), 1);
    Ok(outcome.returns[0]
        .as_int()
        .expect("integer return")
        .as_signed())
}

#[test]
fn fresh_loop_reentry_and_unused_stale_handles_remain_valid_and_execute() {
    for text in [
        include_str!("../fixtures/frame-cfg/fresh_generation_loop.trust_ir"),
        include_str!("../fixtures/frame-cfg/fresh_after_stale_loop.trust_ir"),
    ] {
        let (module, errors) = checked(text);
        assert!(errors.is_empty(), "{errors:?}");
        assert_eq!(
            execute(&module, InterpretValue::int(Ty::I64, 7).unwrap()).unwrap(),
            7
        );
    }
}

#[test]
fn reopened_declaration_does_not_revive_carried_old_generation() {
    let (module, errors) = checked(include_str!(
        "../fixtures/frame-cfg/stale_generation_loop.trust_ir"
    ));
    assert!(errors.iter().any(|e| matches!(
        e,
        ValidationError::BindingUseAfterClose {
            block: 3,
            frame_value: 13
        }
    )));
    assert_ub(
        &execute(&module, InterpretValue::int(Ty::I64, 7).unwrap()).unwrap_err(),
        "LoadSlot: frame is not open",
    );
}

#[test]
fn every_join_signature_is_checked_without_last_writer_selection() {
    let (mixed, errors) = checked(include_str!(
        "../fixtures/frame-cfg/mixed_origin_join.trust_ir"
    ));
    assert!(errors.iter().any(|e| matches!(
        e,
        ValidationError::BindingSlotTypeMismatch { frame_id: 0, .. }
    )));
    let mismatch = execute(&mixed, InterpretValue::bool(true)).unwrap_err();
    assert_eq!(mismatch.code, InterpretErrorCode::TypeError);
    // The carried frame retains its original source slot declaration.
    assert!(
        mismatch
            .message
            .contains("LoadSlot: requested type differs from source slot"),
        "{mismatch:?}"
    );
    assert_eq!(execute(&mixed, InterpretValue::bool(false)).unwrap(), 8);
    let (same, errors) = checked(include_str!(
        "../fixtures/frame-cfg/same_signature_join.trust_ir"
    ));
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(execute(&same, InterpretValue::bool(true)).unwrap(), 7);
    assert_eq!(execute(&same, InterpretValue::bool(false)).unwrap(), 8);
}

#[test]
fn read_write_and_double_close_after_an_edge_are_refused_and_remain_runtime_ub() {
    for (operation, message) in [
        (
            "%3 = load_slot u64 %2, 0\n  ret %3",
            "LoadSlot: frame is not open",
        ),
        (
            "%3 = bind_slot %2, 0, %0\n  ret %0",
            "BindSlot: frame is not open",
        ),
        (
            "close_frame %2\n  ret %0",
            "CloseFrame: frame is not open (double close)",
        ),
    ] {
        let text = format!(
            "module \"closed_edge\"\nfuncty.0 = (u64) -> (u64)\nfn @main(functy.0) {{\nbb0(%0: u64):\n  %1 = open_frame #0 \"frame\" {{x: u64}}\n  %2 = bind_slot %1, 0, %0\n  close_frame %1\n  br bb1()\nbb1:\n  {operation}\n}}\n"
        );
        let (module, errors) = checked(&text);
        assert!(errors.iter().any(|e| matches!(
            e,
            ValidationError::BindingUseAfterClose {
                block: 1,
                frame_value: 2
            }
        )));
        assert_ub(
            &execute(&module, InterpretValue::int(Ty::U64, 7).unwrap()).unwrap_err(),
            message,
        );
    }
}
