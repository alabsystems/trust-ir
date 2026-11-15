// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::{Block, FuncTyId, InstrNode};

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if self.stop_at == Some(self.events.len()) {
            Err("original validation stop")
        } else {
            Ok(())
        }
    }
}
fn module() -> Module {
    let mut module = Module::new("observed_validation_catalog");
    module
        .func_types
        .push(FuncTy::unrecorded(vec![], vec![], false));
    let mut function = Function::new(FuncId::new(7), "entry", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(7))
}

#[test]
fn full_success_report_and_borrowed_module_are_unchanged() {
    let module = module();
    let baseline = validate_module_report(&module);
    assert!(
        baseline.is_ok(),
        "fixture must not pass through a shared refusal"
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = validate_module_report_with_observed_catalog(&module, &mut session, site())
        .expect("original owner accepts");
    assert_eq!(actual.errors(), baseline.errors());
    assert_eq!(
        actual.replayed_certificate_refs(),
        baseline.replayed_certificate_refs()
    );
    assert_eq!(
        actual.handle_registry_is_pinned(),
        baseline.handle_registry_is_pinned()
    );
    assert!(core::ptr::eq(
        actual.validated_module().expect("fully validated"),
        &module
    ));
}

#[test]
fn structural_refusals_do_not_turn_into_observation_errors_or_authority() {
    let mut module = module();
    module.functions.push(module.functions[0].clone());
    let baseline = validate_module_report(&module);
    assert!(!baseline.is_ok());
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let actual = validate_module_report_with_observed_catalog(&module, &mut session, site())
        .expect("accepting observer does not erase structural refusal");
    assert_eq!(actual.errors(), baseline.errors());
    assert!(actual.validated_module().is_none());
}

#[test]
fn every_actual_poll_including_report_publication_is_a_typed_terminal_stop() {
    let module = module();
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert!(validate_module_report_with_observed_catalog(&module, &mut session, site()).is_ok());
    let polls = observer.events.len();
    assert_eq!(polls, module.functions.len() + 4);
    for stop_at in 1..=polls {
        let mut observer = Observer {
            stop_at: Some(stop_at),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(matches!(
            validate_module_report_with_observed_catalog(&module, &mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            session.first_refusal().expect("typed cause").cause,
            "original validation stop"
        );
        assert!(
            validate_module_report_with_observed_catalog(&module, &mut session, site()).is_err()
        );
        assert_eq!(
            observer
                .events
                .iter()
                .filter(|event| event.phase != ExecutionPhase::ScratchRetirement)
                .count(),
            stop_at,
        );
    }
}
