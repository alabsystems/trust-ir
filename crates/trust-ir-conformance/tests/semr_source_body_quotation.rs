// Copyright 2026 Andrew Yates. Apache-2.0.
//! Exact custody between producer bytes and independently checked Lean literals.
//! This is not a MIR quotation theorem or source proof certificate.

#[test]
fn checked_lean_literals_are_the_original_and_body_mutant_wire_images() {
    let lean = include_str!("../../../lean/semr/SemRSourceBodyCheck.lean");
    for (name, wire) in [
        (
            "originalBytes",
            include_bytes!("../../../lean/semr/fixtures/law-proof-ref-original.tmbc").as_slice(),
        ),
        (
            "mutantBytes",
            include_bytes!("../../../lean/semr/fixtures/law-proof-ref-body-mutant.tmbc").as_slice(),
        ),
    ] {
        let prefix = format!("def {name} : List Nat := ");
        let literal = lean.split_once(&prefix).unwrap().1.lines().next().unwrap();
        let bytes: Vec<u8> = serde_json::from_str(literal).unwrap();
        assert_eq!(bytes, wire, "Lean checked a different byte image: {name}");
        let module = trust_ir::binary::deserialize_module(wire).unwrap();
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.structs.len(), 1);
        assert_eq!(module.structs[0].fields.len(), 1);
        assert_eq!(module.structs[0].fields[0].ty, trust_ir::ty::Ty::I64);
    }
}
