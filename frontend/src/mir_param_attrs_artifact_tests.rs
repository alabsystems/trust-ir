// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Observe the real MIR producer's raw owner, not a reparsed artifact that
//! already lost its slot table. The existing pair-param acceptance separately
//! checks interpreter/native results and source-span custody.

use super::*;
use std::path::Path;
use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::{Function, Inst, Module, ParamAttrs, Ty as IrTy};

struct ActualOwnerChecks {
    ran: bool,
}

fn emitted<'a>(module: &'a Module, symbol: &str) -> &'a Function {
    let matches = module
        .functions
        .iter()
        .filter(|function| function.name == symbol)
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "one original instance owns {symbol}");
    matches[0]
}

fn closure_body_name(tcx: TyCtxt<'_>, instance: Instance<'_>) -> String {
    // This fixture selects plain, local, nongeneric Item instances. Closure
    // members intentionally keep the producer's readable def-path spelling;
    // the member-discovery ledger uses mangled symbols only for instance keys
    // and FuncId wiring. The single-function artifact route is different.
    assert!(instance.def_id().is_local());
    assert!(instance.args.is_empty());
    tcx.def_path_str(instance.def_id())
        .replace("::", "__")
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' || character == '.' {
                character
            } else {
                '_'
            }
        })
        .collect()
}

impl Callbacks for ActualOwnerChecks {
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        self.ran = true;
        let mono = tcx.collect_and_partition_mono_items(());
        let mut instances = Vec::new();
        for cgu in mono.codegen_units {
            for (item, _) in cgu.items_in_deterministic_order(tcx) {
                let MonoItem::Fn(instance) = item else {
                    continue;
                };
                if !matches!(instance.def, ty::InstanceKind::Item(_))
                    || !instance.def_id().is_local()
                {
                    continue;
                }
                let name = tcx.item_name(instance.def_id()).to_string();
                if ["param_trip", "mk_big", "big_first"].contains(&name.as_str()) {
                    instances.push((name, instance));
                }
            }
        }
        let actual = |name: &str| {
            let rows = instances
                .iter()
                .filter(|(candidate, _)| candidate == name)
                .collect::<Vec<_>>();
            assert_eq!(rows.len(), 1, "the actual source has one {name} instance");
            rows[0].1
        };
        let root = actual("param_trip");
        let mk_big = actual("mk_big");
        let big_first = actual("big_first");
        let producer_body = tcx.instance_mir(mk_big.def);
        assert_eq!(producer_body.arg_count, 1);
        assert_eq!(
            producer_body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty,
            tcx.types.u64
        );
        assert!(matches!(
            producer_body.local_decls[rustc_middle::mir::RETURN_PLACE]
                .ty
                .kind(),
            ty::Adt(..)
        ));

        let (module, errors, members) =
            mir_lower::lower_closure_for_emit(tcx, root, tcx.instance_mir(root.def))
                .expect("the actual source closure lowers");
        assert!(errors.is_empty(), "{errors:?}");
        let mk_symbol = tcx.symbol_name(mk_big).name.to_string();
        let first_symbol = tcx.symbol_name(big_first).name.to_string();
        let root_symbol = tcx.symbol_name(root).name.to_string();
        assert!(members.contains(&mk_symbol));
        assert!(members.contains(&first_symbol));
        let producer = emitted(&module, &closure_body_name(tcx, mk_big));
        let consumer = emitted(&module, &closure_body_name(tcx, big_first));
        assert!(!producer.blocks.is_empty());
        assert!(!consumer.blocks.is_empty());
        let producer_signature = module.func_type(producer.ty).unwrap();
        assert_eq!(producer_signature.params, [IrTy::Ptr, IrTy::U64]);
        assert!(producer_signature.returns.is_empty());
        assert_eq!(
            producer.attrs.params,
            [
                ParamAttrs {
                    sret: true,
                    ..Default::default()
                },
                ParamAttrs::default()
            ]
        );
        assert_eq!(module.func_type(consumer.ty).unwrap().params, [IrTy::Ptr]);
        assert_eq!(
            consumer.attrs.params,
            [ParamAttrs {
                byval: true,
                ..Default::default()
            }]
        );
        assert!(members.contains(&root_symbol));
        let caller = emitted(&module, &closure_body_name(tcx, root));
        assert!(!caller.blocks.is_empty());
        for actual_callee in [producer.id, consumer.id] {
            assert!(
                caller.instructions().any(|node| matches!(&node.inst,
                Inst::Call { callee, .. } if *callee == actual_callee)),
                "original call binds actual {actual_callee:?}"
            );
        }

        // Observe the raw owner BEFORE the driver's declared file-table
        // basename rewrite. Neither SSA IDs, attributes nor metadata are
        // canonicalized or stripped to make transport succeed.
        let retained = module.clone();
        assert!(trust_ir::text_loss::text_losses(&module).is_empty());
        let text = module.to_string();
        assert!(text.lines().any(|line| line.trim() == "; #param_attrs 1:"));
        let parsed = trust_ir::parser::parse_module(&text).expect("raw actual owner re-parses");
        assert_eq!(parsed, module);
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(serialize_module(&parsed).expect("serialize_module: test fixture"), bytes);
        assert_eq!(deserialize_module(&bytes).unwrap(), module);
        assert_eq!(module, retained);
        let mut shortened = retained;
        shortened
            .function_by_id_mut(producer.id)
            .unwrap()
            .attrs
            .params
            .pop();
        assert_ne!(
            serialize_module(&shortened).expect("serialize_module: test fixture"),
            bytes,
            "dropping the default is not raw custody"
        );
        Compilation::Stop
    }
}

#[test]
fn actual_pair_param_mir_owner_keeps_sret_default_tail_and_call_identity_through_text() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/pair_param_corpus.rs");
    let mut args = vec![
        "trust_ir_mir".into(),
        fixture.display().to_string(),
        "--crate-type=lib".into(),
        "-Ztrust-verify=off".into(),
    ];
    // Exactly the maintained artifact-only source lane and existing opt-in
    // pair ABI. This is codec/lowering evidence, never verified compilation.
    trust_ir_frontend::append_matching_rustc_sysroot(&mut args)
        .expect("matching installed Trust compiler");
    mir_lower::enable_pair_ret_by_value();
    let mut checks = ActualOwnerChecks { ran: false };
    rustc_driver::run_compiler(&args, &mut checks);
    assert!(
        checks.ran,
        "the actual source/compiler-context consumer must execute"
    );
}
