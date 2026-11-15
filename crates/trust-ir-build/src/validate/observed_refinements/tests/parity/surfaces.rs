// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn global_drop_glue_closure_capture_and_all_signature_occurrences_keep_exact_full_order() {
    let mut m = module();
    let bad = Ty::Refine(TyId::new(99), PredId::new(99));
    m.globals.push(trust_ir::Global {
        name: "G'λ\0".into(),
        ty: bad.clone(),
        mutable: false,
        initializer: None,
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    m.drop_glue.push(trust_ir::DropGlueEntry {
        glue: FuncId::new(99),
        ty: bad.clone(),
    });
    m.closure_types.push(trust_ir::ty::ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![bad.clone()],
    });
    m.func_types[0].params = vec![bad.clone()];
    m.func_types[0].returns = vec![bad];
    let (errors, _, _) = run(&m);
    let locations = errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::RefinementTypeInvalid { location, .. } => Some(location.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        locations,
        vec![
            "functy.0 param 0",
            "functy.0 return 0",
            "global 'G'λ\0'",
            "drop_glue row 0",
            "closurety.0 capture 0"
        ]
    );
}
