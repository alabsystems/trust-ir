// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn direct_and_cannot_unwind_calls_map_parameter_and_global_sides_without_losing_callee_flags() {
    for boundary in [false, true] {
        let instruction = if boundary {
            Inst::CallCannotUnwind {
                callee: FuncId::new(7),
                args: vec![v(2)],
            }
        } else {
            Inst::Call {
                callee: FuncId::new(7),
                args: vec![v(2)],
            }
        };
        let (mut m, f) = fixture(vec![node(instruction, &[])]);
        let mut effects = EffectSummary::pure()
            .reading(EffectSet::of([p(0)]))
            .writing(EffectSet::of([g(u32::MAX)]));
        effects.allocates = true;
        effects.frees = true;
        effects.may_unwind = true;
        effects.io = true;
        callee(&mut m, 7, effects, false);
        let out = run(&m, &f, ImportPolicy::Structural).0;
        assert_eq!(out.len(), 6);
        assert!(
            matches!(&out[0],ValidationError::EffectSummaryViolated {inst,..} if inst.contains("(callee reads *param0) through *param1"))
        );
        assert!(
            matches!(&out[4],ValidationError::EffectSummaryViolated {effect:"may_unwind",inst,..} if inst.ends_with(", whose callee may unwind"))
        );
    }
}
#[test]
fn missing_argument_and_seqmap_internal_slot_force_everything_even_for_local_values() {
    for inst in [
        Inst::Call {
            callee: FuncId::new(7),
            args: vec![],
        },
        Inst::SeqMap {
            ty: Ty::Sequence(TyId::new(0)),
            seq: v(1),
            fwd: FuncId::new(7),
        },
    ] {
        let (mut m, f) = fixture(vec![node(alloca(), &[3]), node(inst, &[])]);
        callee(
            &mut m,
            7,
            EffectSummary::pure().reading(EffectSet::of([p(0)])),
            false,
        );
        let out = run(&m, &f, ImportPolicy::Refuse).0;
        assert_eq!(out.len(), 1);
        assert!(
            matches!(&out[0],ValidationError::EffectSummaryViolated {inst,..} if inst.contains("an argument this trace cannot follow"))
        );
    }
}
#[test]
fn all_nine_linkages_and_missing_effect_summaries_preserve_the_original_top_rule() {
    for linkage in [
        trust_ir::Linkage::External,
        trust_ir::Linkage::Internal,
        trust_ir::Linkage::Private,
        trust_ir::Linkage::AvailableExternally,
        trust_ir::Linkage::WeakOdr,
        trust_ir::Linkage::LinkOnceOdr,
        trust_ir::Linkage::Weak,
        trust_ir::Linkage::LinkOnce,
        trust_ir::Linkage::ExternalWeak,
    ] {
        let (mut m, f) = fixture(vec![node(
            Inst::Call {
                callee: FuncId::new(7),
                args: vec![],
            },
            &[],
        )]);
        callee(&mut m, 7, EffectSummary::pure(), false);
        m.functions[1].linkage = linkage;
        let out = run(&m, &f, ImportPolicy::Structural).0;
        assert_eq!(
            out.len(),
            if matches!(
                linkage,
                trust_ir::Linkage::Weak
                    | trust_ir::Linkage::LinkOnce
                    | trust_ir::Linkage::ExternalWeak
            ) {
                6
            } else {
                0
            }
        );
        m.functions[1].summary.as_mut().unwrap().effects = None;
        assert_eq!(run(&m, &f, ImportPolicy::Refuse).0.len(), 6);
    }
}
#[test]
fn sited_panic_operands_then_global_location_preserve_exact_call_argument_mapping() {
    let site = PanicSite {
        entry: FuncId::new(7),
        location: PanicLocation::Global(GlobalId::new(9)),
    };
    let (mut m, mut f) = fixture(vec![node(
        Inst::Assert {
            cond: v(9),
            kind: AssertKind::BoundsCheck {
                index: v(1),
                len: v(2),
            },
            site: Some(site),
        },
        &[],
    )]);
    callee(
        &mut m,
        7,
        EffectSummary::pure().reading(EffectSet::of([p(0), p(1), p(2)])),
        false,
    );
    let out = run(&m, &f, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 3);
    assert!(
        matches!(&out[2],ValidationError::EffectSummaryViolated {inst,..} if inst=="assert (its failure's panic call) (callee reads *param2, which is global #9)")
    );
    f.summary.as_mut().unwrap().effects =
        Some(EffectSummary::pure().reading(EffectSet::of([p(0), p(1), g(9)])));
    assert!(run(&m, &f, ImportPolicy::Structural).0.is_empty());
}
#[test]
fn invoke_and_assert_invoke_record_their_own_unwind_before_any_callee_reason() {
    let site = PanicSite {
        entry: FuncId::new(7),
        location: PanicLocation::Value(v(1)),
    };
    for inst in [
        Inst::Invoke {
            callee: FuncId::new(7),
            args: vec![v(1)],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
        },
        Inst::AssertInvoke {
            cond: v(9),
            kind: AssertKind::NullPtr,
            site,
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
        },
    ] {
        let name = instruction_kind(&inst);
        let (mut m, f) = fixture(vec![node(inst, &[])]);
        callee(&mut m, 7, EffectSummary::top(), false);
        let out = run(&m, &f, ImportPolicy::Structural).0;
        assert_eq!(out.len(), 6);
        assert!(
            matches!(&out[4],ValidationError::EffectSummaryViolated {effect:"may_unwind",inst,..} if inst==name)
        );
    }
}
#[test]
fn recursive_definition_and_unbacked_declaration_follow_the_same_enclosing_body_premise() {
    let (mut m, mut f) = fixture(vec![node(
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![v(1), v(2)],
        },
        &[],
    )]);
    f.summary.as_mut().unwrap().effects = Some(EffectSummary::top());
    m.functions[0] = f.clone();
    assert!(run(&m, &f, ImportPolicy::Structural).0.is_empty());
    let (mut m, f) = fixture(vec![node(
        Inst::Call {
            callee: FuncId::new(7),
            args: vec![v(1)],
        },
        &[],
    )]);
    callee(&mut m, 7, EffectSummary::pure(), true);
    assert_eq!(run(&m, &f, ImportPolicy::Structural).0.len(), 6);
    assert_eq!(run(&m, &f, ImportPolicy::Refuse).0.len(), 6);
}
