// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use std::cmp::Ordering::{self, Equal, Greater, Less};
use trust_ir::inst::{CastOp, ICmpOp};
use trust_ir::value::FuncId;
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

fn expected(op: ICmpOp, unsigned: Ordering, signed: Ordering) -> bool {
    match op {
        ICmpOp::Eq => unsigned == Equal,
        ICmpOp::Ne => unsigned != Equal,
        ICmpOp::Ult => unsigned == Less,
        ICmpOp::Ule => unsigned != Greater,
        ICmpOp::Ugt => unsigned == Greater,
        ICmpOp::Uge => unsigned != Less,
        ICmpOp::Slt => signed == Less,
        ICmpOp::Sle => signed != Greater,
        ICmpOp::Sgt => signed == Greater,
        ICmpOp::Sge => signed != Less,
    }
}

fn pointer_comparison_module(bits: u32) -> (Module, Vec<(FuncId, Option<bool>)>) {
    let mut mb =
        ModuleBuilder::new_with_target_info(format!("pointer_compare_{bits}"), semr_target(bits));
    let sig = mb.add_func_type(vec![], vec![Ty::Bool]);
    let integer = if bits == 32 { Ty::U32 } else { Ty::U64 };
    let mut runs = Vec::new();
    for pair in 0..7 {
        for op in [
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
        ] {
            let mut fb = mb.function(format!("pair_{pair}_{op:?}"), sig);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let (lhs, rhs, unsigned, signed) = match pair {
                0 => (fb.null_ptr(), fb.null_ptr(), Equal, Equal),
                1 => {
                    let pointer = fb.alloca(Ty::U8);
                    (pointer, fb.copy(Ty::Ptr, pointer), Equal, Equal)
                }
                2 => (fb.alloca(Ty::U8), fb.alloca(Ty::U8), Less, Less),
                3 => {
                    let first = fb.alloca(Ty::U8);
                    let second = fb.alloca(Ty::U8);
                    (second, first, Greater, Greater)
                }
                4 => (fb.null_ptr(), fb.alloca(Ty::U8), Less, Less),
                5 => {
                    let high = fb.iconst(integer.clone(), 1i128 << (bits - 1));
                    let high = fb.cast(CastOp::IntToPtr, integer.clone(), Ty::Ptr, high);
                    (high, fb.null_ptr(), Greater, Less)
                }
                6 => {
                    let one = fb.iconst(integer.clone(), 1);
                    let two = fb.iconst(integer.clone(), 2);
                    let one = fb.cast(CastOp::IntToPtr, integer.clone(), Ty::Ptr, one);
                    let two = fb.cast(CastOp::IntToPtr, integer.clone(), Ty::Ptr, two);
                    (one, two, Less, Less)
                }
                _ => unreachable!(),
            };
            let result = fb.icmp(op, Ty::Ptr, lhs, rhs);
            fb.ret(vec![result]);
            runs.push((fb.build(), Some(expected(op, unsigned, signed))));
        }
    }
    let mut fb = mb.function("poison_pointer_compare_is_ub", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let poison = fb.undef(Ty::Ptr);
    let null = fb.null_ptr();
    let result = fb.icmp(ICmpOp::Eq, Ty::Ptr, poison, null);
    fb.ret(vec![result]);
    runs.push((fb.build(), None));
    let module = mb.build().expect("pointer comparison module");
    assert_eq!(runs.len(), 71);
    (module, runs)
}

#[test]
fn pointer_comparisons_use_target_addresses_across_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        let (module, runs) = pointer_comparison_module(bits);
        let binary = trust_ir::binary::serialize_module(&module).expect("encode binary");
        let text = trust_ir::format::text_checked(&module).expect("encode text");
        let json = serde_json::to_vec(&module).expect("encode JSON");
        let msgpack = rmp_serde::to_vec(&module).expect("encode MessagePack");
        for (format, decoded) in [
            ("original", module),
            (
                "binary",
                trust_ir::binary::deserialize_module(&binary).expect("decode binary"),
            ),
            (
                "text",
                trust_ir::parser::parse_module(&text).expect("decode text"),
            ),
            ("JSON", serde_json::from_slice(&json).expect("decode JSON")),
            (
                "MessagePack",
                rmp_serde::from_slice(&msgpack).expect("decode MessagePack"),
            ),
        ] {
            let errors = trust_ir_build::validate_module(&decoded);
            assert!(errors.is_empty(), "{bits}/{format}: {errors:?}");
            modules.push((
                format!("pointer_compare_{bits}_{format}"),
                decoded,
                runs.clone(),
            ));
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runs)| Batch {
            label: label.clone(),
            module,
            runs: runs.iter().map(|(func, _)| (*func, vec![])).collect(),
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 710);
    let mut counts = (0, 0);
    for (report, (_, value)) in reports
        .iter()
        .zip(modules.iter().flat_map(|(_, _, runs)| runs))
    {
        if let Some(value) = value {
            let expected = Verdict::Ok(vec![Val::Bool(*value)]);
            assert_eq!(report.rust, expected, "{report:?}");
            assert_eq!(report.lean, expected, "{report:?}");
            counts.0 += 1;
        } else {
            assert!(matches!(report.rust, Verdict::Ub(_)), "{report:?}");
            assert!(matches!(report.lean, Verdict::Ub(_)), "{report:?}");
            counts.1 += 1;
        }
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
    assert_eq!(counts, (700, 10));
}
