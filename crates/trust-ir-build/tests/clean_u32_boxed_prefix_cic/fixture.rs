// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use trust_ir::clean_boxed_u32::RuntimeSources;
use trust_ir::{FuncId, Module};
use trust_ir_build::clean_kernel::{Declaration, Environment, Expr, Name};
use trust_ir_build::core_execution::Limits;
use trust_ir_build::{
    CheckedSourceValueOperational,
    check_u32_straight_line_source_value_with_validated_runtime_context,
    check_uint_source_value_equation,
};
const ORIGINAL: &[u8] =
    include_bytes!("../fixtures/source_value_equations/boundActualEquation/module.bin");
pub(super) fn fixture() -> Module {
    let module = trust_ir::binary::deserialize_module(ORIGINAL).unwrap();
    assert_eq!(
        trust_ir::binary::serialize_module(&module).unwrap(),
        ORIGINAL
    );
    assert_eq!((module.functions.len(), module.func_types.len()), (72, 73));
    assert_eq!(
        (
            module.proof_obligations.len(),
            module.proof_certificates.len()
        ),
        (1, 1)
    );
    module
}
pub(super) fn subject(module: Module, run: impl FnOnce(&CheckedSourceValueOperational<'_>)) {
    macro_rules! data {
        ($file:literal) => {
            include_bytes!(concat!(
                "../fixtures/source_value_equations/boundActualEquation/",
                $file
            ))
        };
    }
    fn expression(raw: &[u8]) -> Expr {
        trust_ir::proof::decode_clean_expr_v1(raw).unwrap()
    }
    fn name(raw: &[u8]) -> Name {
        let e = expression(raw);
        let trust_ir_build::clean_kernel::ExprKind::Const(n, levels) = e.kind() else {
            panic!("name carrier")
        };
        assert!(levels.is_empty());
        n.clone()
    }
    let mut environment = Environment::with_prelude();
    environment
        .add_decl(Declaration::Definition {
            name: name(data!("definition-0.name.bin")),
            level_params: vec![],
            type_: expression(data!("definition-0.type.bin")),
            value: expression(data!("definition-0.value.bin")),
            is_reducible: false,
        })
        .unwrap();
    let source = name(data!("definition-0.name.bin"));
    assert_eq!(
        environment.closure_digest(&source).unwrap().as_slice(),
        data!("source-closure-digest.bin")
    );
    let theorem = Declaration::Theorem {
        name: name(data!("theorem.name.bin")),
        level_params: vec![],
        type_: expression(data!("theorem.type.bin")),
        value: expression(data!("theorem.value.bin")),
    };
    // Real shared-reader success is mandatory, including the original metadata tables.
    let source =
        check_uint_source_value_equation(&module, FuncId(70), &environment, &source, &theorem)
            .unwrap();
    let addresses: Vec<_> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, 4096 + 8 * i as u64))
        .collect();
    let operational = check_u32_straight_line_source_value_with_validated_runtime_context(
        &source,
        &addresses,
        Limits {
            max_operations: 20000,
            max_locals: 4096,
            max_list_items: 4096,
            max_lookup_candidates: 1024,
            lookup_heartbeats: 1000000,
            lookup_cache_entries: 100000,
        },
    )
    .unwrap();
    assert!(core::ptr::eq(operational.source_value().module(), &module));
    assert!(core::ptr::eq(
        operational
            .retained_validation_report()
            .unwrap()
            .validated_module()
            .unwrap(),
        &module
    ));
    run(&operational);
}
pub(super) fn runtime_sources() -> RuntimeSources<'static> {
    RuntimeSources {
        object_model: include_bytes!(
            "../../../trust-ir/tests/fixtures/clean_uint32_runtime/object_model.rs.txt"
        ),
        ctor_scalar: include_bytes!(
            "../../../trust-ir/tests/fixtures/clean_uint32_runtime/ctor_scalar.rs.txt"
        ),
        rc_core: include_bytes!(
            "../../../trust-ir/tests/fixtures/clean_uint32_runtime/rc_core.rs.txt"
        ),
        refcount: include_bytes!(
            "../../../trust-ir/tests/fixtures/clean_uint32_runtime/refcount.rs.txt"
        ),
        public_api: include_bytes!(
            "../../../trust-ir/tests/fixtures/clean_uint32_runtime/public_api.rs.txt"
        ),
    }
}
