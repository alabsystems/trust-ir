// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
#[path = "../../trust-ir-conformance/tests/generate/signature_abi.rs"]
mod fixture;
use trust_ir::{ArgExt, BlockId, FuncId, FuncTyId, Function, ParamAttrs};
use trust_ir_build::{ValidationError, validate_module};

#[test]
fn validator_checks_every_typed_signature_even_without_a_function_declaration() {
    let module = fixture::module().expect("signature_abi::module: test fixture");
    assert!(validate_module(&module).is_empty());
    let mut missing = module.clone();
    missing.func_types[0].abi.as_mut().unwrap().arguments[2]
        .bindings
        .pop();
    let mut target = module.clone();
    target.target_info.as_mut().unwrap().pointer_size = 4;
    for mutant in [missing, target] {
        assert!(
            validate_module(&mutant)
                .iter()
                .any(|error| matches!(error, ValidationError::InvalidSignatureAbi { .. }))
        );
    }
}
#[test]
fn validator_reconciles_legacy_function_claims_with_the_typed_signature() {
    let mut module = fixture::module().expect("signature_abi::module: test fixture");
    let mut function = Function::new(FuncId::new(0), "callee", FuncTyId::new(0), BlockId::new(0));
    function.attrs.params = vec![ParamAttrs::default(); 6];
    function.attrs.params[0].sret = true;
    function.attrs.params[1].ext = ArgExt::SignExt;
    module.functions.push(function);
    assert!(
        validate_module(&module).is_empty(),
        "{:?}",
        validate_module(&module)
    );
    module.functions[0].attrs.params[1].ext = ArgExt::ZeroExt;
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::InvalidSignatureAbi { .. }))
    );
}

#[test]
fn oversized_unused_descriptor_refuses_before_linked_root_identity() {
    use trust_ir::proof::RejectingModuleProofAuthority;
    use trust_ir_build::{ModuleSet, validate_linked_module};
    let module = fixture::module().expect("signature_abi::module: test fixture");
    let none = ModuleSet::new(std::iter::empty::<&trust_ir::Module>());
    let accepted = validate_linked_module(&module, &none, &RejectingModuleProofAuthority);
    assert!(accepted.is_ok(), "{:?}", accepted.errors());

    let mut mutant = module.clone();
    mutant.func_types.push(mutant.func_types[0].clone());
    mutant.func_types[1].abi.as_mut().unwrap().frontend.revision =
        "x".repeat(trust_ir::signature_abi::MAX_ABI_TEXT_BYTES + 1);
    let rejected = validate_linked_module(&mutant, &none, &RejectingModuleProofAuthority);
    assert_eq!(rejected.errors().len(), 1, "{:?}", rejected.errors());
    assert!(matches!(
        &rejected.errors()[0],
        ValidationError::ModuleHasNoWireIdentity { location, construct }
            if location == "signature #1" && construct.contains("ABI")
    ));
    assert_eq!(
        trust_ir_build::wire_identity_blocker(&mutant),
        Some(rejected.errors()[0].clone())
    );
}
