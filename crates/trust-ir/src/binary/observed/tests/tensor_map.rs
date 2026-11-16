// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::{CastOp, Inst, TensorMapNode, ValueId};

fn cast_module() -> Module {
    let input = Ty::Tensor(Box::new(Ty::U32), 1);
    let output = Ty::Tensor(Box::new(Ty::U64), 1);
    let mut module = Module::new("tensor_map_cast");
    module.func_types.push(FuncTy::unrecorded(
        vec![input.clone()],
        vec![output.clone()],
        false,
    ));
    let mut function = Function::new(
        FuncId::new(0),
        "tensor_map_cast",
        FuncTyId::new(0),
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), input));
    block.body.push(
        InstrNode::new(Inst::TensorMap {
            ty: output,
            args: vec![ValueId::new(0)],
            body: vec![TensorMapNode::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U32,
                dst_ty: Ty::U64,
                operand: 0,
            }],
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

#[test]
fn tensor_map_cast_wire_identity_keeps_both_types_and_every_original_stop() {
    let module = cast_module();
    for scheme in [IdentityScheme::V2, IdentityScheme::V3] {
        let mut baseline = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
        assert_eq!(
            observed_module_identity(&module, scheme, &mut session, site()).unwrap(),
            module.stable_digest_under(scheme)
        );
        for stop in 1..=baseline.events.len() {
            let mut observer = Observer {
                stop_at: Some(stop),
                ..Observer::default()
            };
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                observed_module_identity(&module, scheme, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused),
                "cut {stop}"
            );
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
            assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
            assert!(observed_module_identity(&module, scheme, &mut session, site()).is_err());
            assert_eq!(session.first_refusal().unwrap().cause, "interior");
            assert!(
                observer.events[stop..]
                    .iter()
                    .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}

#[test]
fn tensor_map_cast_collection_keeps_cumulative_work_and_copy_budgets() {
    let module = cast_module();
    let mut baseline = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    module.stable_digest_observed(&mut session, site()).unwrap();
    for bytes in [false, true] {
        let mut observer = Observer {
            work_limit: (!bytes).then_some(baseline.work),
            byte_limit: bytes.then_some(baseline.bytes),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        module.stable_digest_observed(&mut session, site()).unwrap();
        assert_eq!(
            module.stable_digest_observed(&mut session, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            if bytes { "bytes" } else { "work" }
        );
        assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
