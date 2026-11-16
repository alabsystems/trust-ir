// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;

fn fixture() -> Module {
    let mut module = Module::new("fn_item_codec");
    let target_signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U32],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    for id in [7, 19] {
        let mut function = Function::new(
            FuncId::new(id),
            format!("target_{id}"),
            target_signature,
            BlockId::new(0),
        );
        function.blocks = vec![Block {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(i128::from(id)),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        }];
        module.try_add_function(function).unwrap();
    }
    // Same signature, distinct item identities, and a reified pointer type.
    module.types.push(Ty::Tuple(vec![
        Ty::FnItem(FuncId::new(7)),
        Ty::FnItem(FuncId::new(19)),
        Ty::Func(target_signature),
    ]));
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::FnItem(FuncId::new(7))],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let mut holder = Function::new(FuncId::new(41), "item", signature, BlockId::new(0));
    holder.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::FnItem(FuncId::new(7)),
                value: Constant::FnItem(FuncId::new(7)),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    }];
    module.try_add_function(holder).unwrap();
    module
}

#[test]
fn fn_item_identity_selects_its_version_and_refuses_both_legacy_projections() {
    let module = fixture();
    let encoded = serialize_module(&module).unwrap();
    assert_eq!(
        &encoded[8..12],
        &FN_ITEM_IDENTITY_FORMAT_VERSION.to_le_bytes()
    );
    assert_eq!(deserialize_module(&encoded).unwrap(), module);
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        assert!(matches!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                ModuleBinaryOptions {
                    body,
                    ..ModuleBinaryOptions::default()
                }
            ),
            Err(BinaryProjectionError::FnItemIdentityRequiresV73)
        ));
    }
    // The feature is selected by use, not by the writer's latest version.
    let legacy = Module::new("no_fn_item");
    assert_eq!(
        &serialize_module(&legacy).unwrap()[8..12],
        &BASE_FORMAT_VERSION.to_le_bytes()
    );
}

#[test]
fn fn_item_wire_tags_are_distinct_read_gated_exact_func_ids() {
    let pool = StringPoolBuilder::new().seal();
    for id in [0, 300, u32::MAX] {
        let mut ty_bytes = Vec::new();
        write_ty(&mut ty_bytes, &pool, &Ty::FnItem(FuncId::new(id)));
        let mut constant_bytes = Vec::new();
        write_constant(
            &mut constant_bytes,
            &pool,
            &Constant::FnItem(FuncId::new(id)),
        );
        assert_eq!(ty_bytes[0], 42);
        assert_eq!(constant_bytes[0], 19);
        let mut reader = Reader::new(&ty_bytes);
        assert_eq!(
            read_ty::<NoExt>(&mut reader).unwrap(),
            Ty::FnItem(FuncId::new(id))
        );
        let mut reader = Reader::new(&constant_bytes);
        assert_eq!(
            read_constant::<NoExt>(&mut reader).unwrap(),
            Constant::FnItem(FuncId::new(id))
        );
        for version in [
            BASE_FORMAT_VERSION,
            TENSOR_FORMAT_VERSION,
            TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION,
            TENSOR_GATHER_SCATTER_FORMAT_VERSION,
            TENSOR_BLOB_FORMAT_VERSION,
            THIN_POINTER_CONTRACT_FORMAT_VERSION,
            UNINHABITED_DIRECT_STORAGE_FORMAT_VERSION,
        ] {
            let mut reader = Reader::new(&ty_bytes);
            reader.version = version;
            assert_eq!(
                read_ty::<NoExt>(&mut reader),
                Err(BinaryError::InvalidTag(42))
            );
            let mut reader = Reader::new(&constant_bytes);
            reader.version = version;
            assert_eq!(
                read_constant::<NoExt>(&mut reader),
                Err(BinaryError::InvalidTag(19))
            );
        }
    }
    let mut bytes = Vec::new();
    write_ty(&mut bytes, &pool, &Ty::Func(FuncTyId::new(300)));
    assert_eq!(bytes, [20, 0xac, 0x02]);
    bytes.clear();
    write_constant(&mut bytes, &pool, &Constant::FnDef(FuncId::new(300)));
    assert_eq!(bytes, [9, 0xac, 0x02]);
}

#[test]
fn fn_item_observed_module_identity_retains_target_and_pointer_distinctions() {
    use crate::interpret::{
        ExecutionObserver, ExecutionProgress, ExecutionSite, InterpretOptions, ObservedSession,
    };
    struct Allow;
    impl ExecutionObserver for Allow {
        type Refusal = ();
        fn admit(&mut self, _: ExecutionProgress) -> Result<(), ()> {
            Ok(())
        }
    }
    let module = fixture();
    for scheme in [IdentityScheme::V2, IdentityScheme::V3] {
        let expected = module.stable_digest_under(scheme);
        let mut observer = Allow;
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            observed::observed_module_identity(
                &module,
                scheme,
                &mut session,
                ExecutionSite::Entry(FuncId::new(41))
            )
            .unwrap(),
            expected
        );
        let mut changed = module.clone();
        changed.types[0] = Ty::FnItem(FuncId::new(19));
        assert_ne!(changed.stable_digest_under(scheme), expected);
        let mut changed = module.clone();
        let Inst::Const { value, .. } = &mut changed.functions[2].blocks[0].body[0].inst else {
            unreachable!()
        };
        *value = Constant::FnDef(FuncId::new(7));
        assert_ne!(changed.stable_digest_under(scheme), expected);
    }
}

#[cfg(all(feature = "parser", feature = "fmt"))]
#[test]
fn fn_item_text_preserves_nonzero_identity_and_refuses_malformed_ids() {
    let module = fixture();
    let text = module.to_string();
    assert!(text.contains("fnitem.7"), "{text}");
    assert!(text.contains("fnitem<func.7>"), "{text}");
    assert!(crate::text_loss::text_losses(&module).is_empty());
    assert_eq!(crate::parser::parse_module(&text).unwrap(), module);
    for malformed in [
        text.replace("fnitem.7", "fnitem.4294967296"),
        text.replace("fnitem<func.7>", "fnitem<func.-1>"),
        text.replace("fnitem<func.7>", "fnitem<functy.7>"),
    ] {
        assert!(crate::parser::parse_module(&malformed).is_err());
    }
}

#[cfg(feature = "serde")]
#[test]
fn fn_item_json_value_and_named_messagepack_preserve_the_full_module() {
    let module = fixture();
    let json = serde_json::to_vec(&module).unwrap();
    assert_eq!(serde_json::from_slice::<Module>(&json).unwrap(), module);
    let value = serde_json::to_value(&module).unwrap();
    assert_eq!(serde_json::from_value::<Module>(value).unwrap(), module);
    let packed = rmp_serde::to_vec_named(&module).unwrap();
    assert_eq!(rmp_serde::from_slice::<Module>(&packed).unwrap(), module);
    assert_eq!(
        serde_json::to_string(&Ty::FnItem(FuncId::new(7))).unwrap(),
        "{\"FnItem\":7}"
    );
    assert_eq!(
        serde_json::to_string(&Constant::FnItem(FuncId::new(7))).unwrap(),
        "{\"FnItem\":7}"
    );
    assert_eq!(
        serde_json::to_string(&Ty::Func(FuncTyId::new(7))).unwrap(),
        "{\"Func\":7}"
    );
    assert_eq!(
        serde_json::to_string(&Constant::FnDef(FuncId::new(7))).unwrap(),
        "{\"FnDef\":7}"
    );
}

#[test]
fn fn_item_native_bundle_binary_transport_keeps_identity_without_authority() {
    use crate::request::{NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle};
    let module = fixture();
    let bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        crate::proof::ProofDigest::zero(),
        module.clone(),
        crate::proof::ProofLineageManifest::new(),
    );
    let bytes = serialize_native_verification_bundle(&bundle).unwrap();
    let back = deserialize_native_verification_bundle(&bytes).unwrap();
    assert_eq!(back.module, module);
    assert_eq!(back.trust_ir_module_digest, bundle.trust_ir_module_digest);
    assert!(back.requests.is_empty());
    assert!(back.evidence_bundles.is_empty());
    assert!(back.lineage.nodes.is_empty());
}
