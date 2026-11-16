// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The real owned scalar-copy primitive must be admitted before construction.
use super::*;
use crate::interpret::observed::value::{clone_value, clone_value_owned};

fn callable_item(id: u32) -> InterpretValue {
    InterpretValue {
        ty: Ty::FnItem(FuncId::new(id)),
        kind: InterpretValueKind::FnItem(FuncId::new(id)),
    }
}

fn callable_pointer(signature: u32, target: u32) -> InterpretValue {
    InterpretValue {
        ty: Ty::Func(FuncTyId::new(signature)),
        kind: InterpretValueKind::FnDef(FuncId::new(target)),
    }
}

#[test]
fn observed_callable_clones_and_equality_preserve_exact_carriers() {
    // Transport preserves opaque identities; these primitives do not resolve a
    // module declaration or admit execution of a function item or null pointer.
    let values = [
        callable_item(7),
        callable_item(8),
        callable_pointer(3, 7),
        callable_pointer(3, 8),
        callable_pointer(4, 7),
        InterpretValue {
            ty: Ty::Func(FuncTyId::new(3)),
            kind: InterpretValueKind::NullPtr,
        },
    ];
    let site = ExecutionSite::Entry(f());
    for value in &values {
        let mut observer = Observer::default();
        let options = InterpretOptions::default();
        let mut session = ObservedSession::new(options, &mut observer);
        assert_eq!(
            clone_value(value, &mut session.structural(site)),
            Ok(value.clone())
        );
        assert_eq!(
            clone_value_owned(value, &mut session.structural_owned(site)),
            Ok(value.clone())
        );
        assert_eq!(
            value.same_observed(value, &mut session.structural(site)),
            Ok(true)
        );
        assert!(session.first_refusal().is_none());
        assert_eq!(session.remaining_fuel(), options.fuel);
        assert_eq!(observer.events.len(), 3);
        for (index, event) in observer.events.iter().enumerate() {
            assert_eq!(event.phase, ExecutionPhase::LiteralElement);
            assert_eq!(event.site, site);
            assert_eq!(event.work, 1);
            assert_eq!(
                event.copy_bytes,
                if index < 2 {
                    core::mem::size_of::<InterpretValue>()
                } else {
                    0
                }
            );
        }
    }
    for (left, right) in [(0, 1), (2, 3), (2, 4), (0, 2), (2, 5)] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            values[left].same_observed(&values[right], &mut session.structural(site)),
            Ok(false)
        );
        assert_eq!(
            values[right].same_observed(&values[left], &mut session.structural(site)),
            Ok(false)
        );
    }
}

#[test]
fn observed_callable_clones_and_equality_reject_cross_kind_and_id_forgeries() {
    let forged = [
        InterpretValue {
            ty: Ty::FnItem(FuncId::new(7)),
            kind: InterpretValueKind::FnDef(FuncId::new(7)),
        },
        InterpretValue {
            ty: Ty::Func(FuncTyId::new(3)),
            kind: InterpretValueKind::FnItem(FuncId::new(7)),
        },
        InterpretValue {
            ty: Ty::FnItem(FuncId::new(7)),
            kind: InterpretValueKind::FnItem(FuncId::new(8)),
        },
        InterpretValue {
            ty: Ty::Ptr,
            kind: InterpretValueKind::FnDef(FuncId::new(7)),
        },
        InterpretValue {
            ty: Ty::FnItem(FuncId::new(7)),
            kind: InterpretValueKind::NullPtr,
        },
        InterpretValue {
            ty: Ty::Func(FuncTyId::new(3)),
            kind: InterpretValueKind::Int(
                crate::interpret::InterpretInt::from_i128(32, true, 7).unwrap(),
            ),
        },
    ];
    let valid = [callable_item(7), callable_pointer(3, 7)];
    let site = ExecutionSite::Entry(f());
    for value in &forged {
        let mut observer = Observer::default();
        let options = InterpretOptions::default();
        let mut session = ObservedSession::new(options, &mut observer);
        assert_eq!(
            clone_value(value, &mut session.structural(site)),
            Err(ObservedValueError::UnsupportedValue)
        );
        assert_eq!(
            clone_value_owned(value, &mut session.structural_owned(site)),
            Err(ObservedValueError::UnsupportedValue)
        );
        assert_eq!(
            value.same_observed(value, &mut session.structural(site)),
            Err(ObservedValueError::UnsupportedValue)
        );
        // A differing type or operand order must not turn a malformed carrier
        // into ordinary inequality before validating its representation.
        for other in &valid {
            assert_eq!(
                value.same_observed(other, &mut session.structural(site)),
                Err(ObservedValueError::UnsupportedValue)
            );
            assert_eq!(
                other.same_observed(value, &mut session.structural(site)),
                Err(ObservedValueError::UnsupportedValue)
            );
        }
        assert!(session.first_refusal().is_none());
        assert_eq!(session.remaining_fuel(), options.fuel);
        assert_eq!(observer.events.len(), 7);
        assert!(observer.events.iter().all(|event| {
            event.phase == ExecutionPhase::LiteralElement && event.site == site && event.work == 1
        }));
    }
}

#[test]
fn observed_callable_carrier_admission_precedes_validation_and_stays_refused() {
    let valid = callable_item(7);
    let forged = InterpretValue {
        ty: Ty::FnItem(FuncId::new(7)),
        kind: InterpretValueKind::FnDef(FuncId::new(7)),
    };
    let site = ExecutionSite::Entry(f());
    for value in [&valid, &forged] {
        for operation in 0..4 {
            let mut observer = Observer {
                stop: Some((ExecutionPhase::LiteralElement, 1)),
                ..Observer::default()
            };
            let options = InterpretOptions::default();
            let mut session = ObservedSession::new(options, &mut observer);
            let result = match operation {
                0 => clone_value(value, &mut session.structural(site)).map(|_| true),
                1 => clone_value_owned(value, &mut session.structural_owned(site)).map(|_| true),
                2 => value.same_observed(&valid, &mut session.structural(site)),
                _ => valid.same_observed(value, &mut session.structural(site)),
            };
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            let expected = ExecutionProgress {
                phase: ExecutionPhase::LiteralElement,
                site,
                work: 1,
                copy_bytes: if operation < 2 {
                    core::mem::size_of::<InterpretValue>()
                } else {
                    0
                },
            };
            let first = session.first_refusal().expect("actual front admission");
            assert_eq!(first.progress, expected);
            assert_eq!(first.cause, "original operation stopped");
            assert_eq!(
                clone_value(&valid, &mut session.structural(site)),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(session.first_refusal().unwrap().progress, expected);
            assert_eq!(session.remaining_fuel(), options.fuel);
            assert_eq!(observer.events, vec![expected]);
        }
    }
}

#[test]
fn actual_callee_scalar_clone_has_its_own_preconstruction_admission() {
    let mut module = program();
    add(
        &mut module,
        0,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![call(1, vec![v(0)], 1), returned(1)],
        false,
    );
    add(
        &mut module,
        1,
        vec![Ty::I32],
        vec![Ty::I32],
        vec![
            node(
                Inst::Copy {
                    ty: Ty::I32,
                    operand: v(0),
                },
                1,
            ),
            returned(1),
        ],
        false,
    );
    let argument = InterpretValue::int(Ty::I32, 7).unwrap();
    let (ordinary, baseline) =
        matching(&module, vec![argument.clone()], InterpretOptions::default());
    assert_eq!(ordinary.steps, 4);
    assert_eq!(ordinary.returns, vec![argument.clone()]);
    let site = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(1),
        block: b(),
        instruction_index: 0,
    });
    let primitives: Vec<_> = baseline
        .events
        .iter()
        .enumerate()
        .filter(|(_, event)| {
            event.site == site
                && event.phase == ExecutionPhase::LiteralElement
                && event.work == 1
                && event.copy_bytes == core::mem::size_of::<InterpretValue>()
        })
        .map(|(index, event)| (index + 1, *event))
        .collect();
    assert_eq!(
        primitives.len(),
        1,
        "actual scalar clone has exactly one front admission"
    );
    struct Stop {
        at: usize,
        seen: usize,
        stopped: bool,
    }
    impl ExecutionObserver for Stop {
        type Refusal = &'static str;
        fn admit(&mut self, _event: ExecutionProgress) -> Result<(), Self::Refusal> {
            self.seen += 1;
            if self.seen == self.at {
                self.stopped = true;
            }
            if self.stopped {
                Err("owned clone front stopped")
            } else {
                Ok(())
            }
        }
    }
    let (at, expected) = primitives[0];
    let mut observer = Stop {
        at,
        seen: 0,
        stopped: false,
    };
    let options = InterpretOptions::default();
    let mut session = ObservedSession::new(options, &mut observer);
    let report =
        Interpreter::with_module(&module).execute_func_observed(f(), vec![argument], &mut session);
    assert!(matches!(report.exit(), ObservedExit::AdmissionRefused));
    assert_eq!(report.steps(), 2);
    assert_eq!(session.remaining_fuel(), options.fuel - 2);
    let first = session
        .first_refusal()
        .expect("actual owned scalar front must be reached");
    assert_eq!(first.progress, expected);
    assert_eq!(first.cause, "owned clone front stopped");
}
