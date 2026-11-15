// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::{Batch, Comparison, Oracle, Val, Verdict, differential, oracle, semr_target};
use trust_ir::inst::{CastOp, ICmpOp};
use trust_ir::value::FuncId;
use trust_ir::{Module, Ty};
use trust_ir_build::ModuleBuilder;

fn allocation_above_function_namespace(bits: u32, count: u32) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info(
        format!("function_namespace_{bits}_{count}"),
        semr_target(bits),
    );
    let unused = mb.add_func_type(vec![], vec![]);
    // Uncalled declarations still occupy module-local code addresses. In
    // particular, the reservation must not count only reachable bodies.
    for index in 0..count - 1 {
        mb.declare_function(format!("unused_{index}"), unused);
    }
    let integer = if bits == 32 { Ty::U32 } else { Ty::U64 };
    let sig = mb.add_func_type(vec![], vec![integer.clone(), Ty::Bool, Ty::Bool, Ty::Bool]);
    let mut fb = mb.function("allocation_above_code", sig);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let data = fb.alloca(Ty::U8);
    let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, integer.clone(), data);
    let last_code = fb.iconst(integer.clone(), i128::from(count));
    let last_code = fb.cast(CastOp::IntToPtr, integer.clone(), Ty::Ptr, last_code);
    let old_floor = fb.iconst(integer.clone(), 1024);
    let old_floor = fb.cast(CastOp::IntToPtr, integer, Ty::Ptr, old_floor);
    let above_code = fb.icmp(ICmpOp::Ugt, Ty::Ptr, data, last_code);
    let above_code_signed = fb.icmp(ICmpOp::Sgt, Ty::Ptr, data, last_code);
    let at_old_floor = fb.icmp(ICmpOp::Eq, Ty::Ptr, data, old_floor);
    fb.ret(vec![address, above_code, above_code_signed, at_old_floor]);
    let runner = fb.build();
    let module = mb.build().expect("function namespace module");
    assert_eq!(module.functions.len(), count as usize);
    (module, runner)
}

#[test]
fn data_allocations_reserve_the_full_function_namespace_across_codecs() {
    let mut modules = Vec::new();
    for bits in [32, 64] {
        for count in [1023, 1024, 1101] {
            let (module, runner) = allocation_above_function_namespace(bits, count);
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
                assert!(errors.is_empty(), "{bits}/{count}/{format}: {errors:?}");
                let expected_address = u128::from(1024.max(count + 1));
                let expected = Verdict::Ok(vec![
                    Val::Int {
                        width: bits,
                        raw: expected_address,
                    },
                    Val::Bool(true),
                    Val::Bool(true),
                    Val::Bool(count == 1023),
                ]);
                modules.push((
                    format!("function_namespace_{bits}_{count}_{format}"),
                    decoded,
                    runner,
                    expected,
                ));
            }
        }
    }
    let Oracle::Ready(exe) = oracle() else { return };
    let batches: Vec<_> = modules
        .iter()
        .map(|(label, module, runner, _)| Batch {
            label: label.clone(),
            module,
            runs: vec![(*runner, vec![])],
        })
        .collect();
    let reports = differential(exe, &batches);
    assert_eq!(reports.len(), 30);
    for (report, (_, _, _, expected)) in reports.iter().zip(&modules) {
        assert_eq!(&report.rust, expected, "{report:?}");
        assert_eq!(&report.lean, expected, "{report:?}");
        assert_eq!(report.comparison, Comparison::Agree, "{report:?}");
    }
}
