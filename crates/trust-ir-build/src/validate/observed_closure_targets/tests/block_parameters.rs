// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

fn merged(right: Option<u32>) -> Function {
    let mut function = fixture();
    let mut entry = function.blocks.pop().unwrap();
    entry.body = vec![constant(10, 99)];
    if let Some(target) = right {
        entry.body.push(constant(20, target));
    }
    entry.body.push(InstrNode::new(Inst::CondBr {
        cond: v(90),
        then_target: BlockId::new(2),
        then_args: vec![v(91), v(10)],
        else_target: BlockId::new(2),
        else_args: vec![v(91), v(20)],
    }));
    let mut merge = Block::new(BlockId::new(2));
    merge.params = vec![(v(30), Ty::U64), (v(31), Ty::Closure(ClosureTyId::new(0)))];
    merge.body = vec![
        copy(32, 31),
        InstrNode::new(Inst::Br {
            target: BlockId::new(3),
            args: vec![v(32)],
        }),
    ];
    let mut forward = Block::new(BlockId::new(3));
    forward
        .params
        .push((v(40), Ty::Closure(ClosureTyId::new(0))));
    forward.body.push(copy(41, 40));
    function.blocks = vec![forward, merge, entry];
    function
}

#[test]
fn all_incoming_edges_exact_positions_and_forwarding_match_observed_walk() {
    for right in [Some(99), Some(100), None] {
        let function = merged(right);
        let targets = super::super::super::local_closure_constant_targets(&function);
        for value in [31, 32, 40, 41] {
            assert_eq!(
                targets.get(&value).copied(),
                right.filter(|target| *target == 99).map(FuncId::new)
            );
        }
        assert!(!targets.contains_key(&30));
        run(&function);
    }
}

#[test]
fn entry_missing_edges_missing_arguments_and_value_cycles_stay_unknown() {
    let good = merged(Some(99));
    let mut cases = Vec::new();
    let mut entry = good.clone();
    entry.entry = BlockId::new(2);
    cases.push(entry);
    let mut no_edges = good.clone();
    no_edges.blocks[2].body.pop();
    cases.push(no_edges);
    let mut missing = good.clone();
    if let Inst::CondBr { else_args, .. } = &mut missing.blocks[2].body.last_mut().unwrap().inst {
        else_args.pop();
    }
    cases.push(missing);
    let mut cycle = good.clone();
    if let Inst::CondBr { else_args, .. } = &mut cycle.blocks[2].body.last_mut().unwrap().inst {
        else_args[1] = v(41);
    }
    cases.push(cycle);
    for function in cases {
        let targets = super::super::super::local_closure_constant_targets(&function);
        for value in [31, 32, 40, 41] {
            assert!(!targets.contains_key(&value));
        }
        run(&function);
    }
}

#[test]
fn block_parameter_observer_refuses_at_every_callback_including_edge_storage() {
    let function = merged(Some(99));
    let (baseline, end) = run(&function);
    for stop in 1..=end {
        let mut observer = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert!(
            matches!(
                ObservedLocalClosureTargets::new_observed(&function, &mut session, site()),
                Err(ObservedValueError::AdmissionRefused)
            ),
            "callback {stop}"
        );
        assert_eq!(
            session.first_refusal().unwrap().cause,
            "original closure target stop"
        );
        drop(session);
        assert_eq!(&observer.events[..stop], &baseline.events[..stop]);
        assert!(
            observer.events[stop..]
                .iter()
                .all(|event| event.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
