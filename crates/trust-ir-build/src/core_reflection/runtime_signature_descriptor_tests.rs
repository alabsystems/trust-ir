// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::ModuleBuilder;
fn target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}
#[test]
fn descriptor_cache_entries_do_not_authorize_scalar_or_nested_float_values() {
    for ty in [Ty::F32, Ty::PtrConst(Box::new(Ty::F32))] {
        let mut builder = ModuleBuilder::new_with_target_info("role_guard", target());
        let sig = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let f = builder.declare_function("float_body", sig);
        let mut body = builder.define_function(f).unwrap();
        let entry = body.create_block();
        let p = body.add_block_param(entry, ty);
        body.switch_to_block(entry);
        body.ret(vec![p]);
        body.build();
        let module = builder.build().unwrap();
        assert!(crate::validate_module(&module).is_empty());
        // All signature descriptors populate the descriptor-role cache BEFORE
        // function reflection checks this actual executable parameter type.
        let error =
            reflect_core_module_with_runtime_signature_descriptors_v1(&module, &[(f, 4096)])
                .unwrap_err();
        assert_eq!(error.to_string(), "unsupported byte-profile type");
        assert!(reflect_core_module_v1(&module, &[(f, 4096)]).is_err());
    }
}
#[test]
fn complete_actual_clean_signature_data_is_compared_without_admitting_its_module() {
    let raw = include_bytes!(
        "../../tests/fixtures/source_value_equations/boundActualEquation/module.bin"
    );
    let module = trust_ir::binary::deserialize_module(raw).unwrap();
    let before = module.clone();
    assert_eq!(module.functions.len(), 72);
    assert_eq!(module.func_types.len(), 73);
    assert_eq!(module.proof_certificates.len(), 1);
    let mut reflection = Reflection {
        module: &module,
        fields: super::runtime_fields::OperationalModuleFields::partition(&module).0,
        retains_release: false,
        memory_index_profile: CoreMemoryIndexProfileV1::StrictI64,
        layout_table: module.layout_table(),
        functions: module.functions.iter().map(|f| (f.id, f)).collect(),
        types: HashMap::new(),
        visiting: HashSet::new(),
        layouts: Vec::new(),
        layout_terms: HashMap::new(),
    };
    fn expected(ty: &Ty) -> Expr {
        match ty {
            Ty::F32 => app("IRTy.float_", [nat(32)]),
            Ty::F64 => app("IRTy.float_", [nat(64)]),
            Ty::Bool => c("IRTy.bool_"),
            Ty::Ptr => c("IRTy.ptr_"),
            Ty::Unit => c("IRTy.unit_"),
            Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 => {
                app("IRTy.uint_", [nat(u64::from(ty.bit_width().unwrap()))])
            }
            Ty::Usize => app("IRTy.usize_", [nat(64)]),
            Ty::Func(id) => app("IRTy.func_", [nat(u64::from(id.index()))]),
            _ => panic!("unexpected retained signature type {ty:?}"),
        }
    }
    // Data-only private probe of the actual production signature constructor.
    // It returns no ReflectedCoreModule, source receipt or executable context.
    for (id, sig) in module.func_types.iter().enumerate() {
        let row = reflection.signature(id, sig, TypeRole::Descriptor).unwrap();
        assert_eq!(
            row,
            app(
                "IRByteSignatureV1.mk",
                [
                    nat(id as u64),
                    list("IRTy", sig.params.iter().map(expected)),
                    list("IRTy", sig.returns.iter().map(expected)),
                    boolean(sig.is_vararg)
                ]
            )
        );
    }
    assert!(module.func_types[35].is_vararg);
    assert_eq!(
        module
            .functions
            .iter()
            .find(|f| f.id.index() == 34)
            .unwrap()
            .ty
            .index(),
        35
    );
    let addresses: Vec<_> = module
        .functions
        .iter()
        .enumerate()
        .map(|(i, f)| (f.id, 4096 + 8 * i as u64))
        .collect();
    assert_eq!(
        reflect_core_module_with_runtime_signature_descriptors_v1(&module, &addresses)
            .unwrap_err()
            .to_string(),
        "module table requires an explicit byte-profile interpretation"
    );
    assert_eq!(module, before);
}
