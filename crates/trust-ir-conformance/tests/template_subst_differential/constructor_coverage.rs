// Copyright 2026 Andrew Yates | Apache-2.0
//! Additive population for constructors absent from the original generator.
//! Storage is transported as raw type geometry; this grants no by-value,
//! allocation, initialized-image, function-header or source authority.

use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};
use trust_ir::{FuncId, HoleId, ParamId, StorageLayout};

struct CheckedCase {
    case: Case,
    expected: Option<Ty>,
}

fn checked(
    label: String,
    ty: TyG<TemplateRef>,
    params: Vec<Option<Ty>>,
    holes: Vec<Option<Ty>>,
    expected: Option<Ty>,
) -> CheckedCase {
    CheckedCase {
        case: Case {
            label,
            ty,
            params,
            holes,
        },
        expected,
    }
}

fn positive_cases() -> Vec<CheckedCase> {
    let mut leaves = Vec::new();
    for id in [0, 1, 11, 53, u32::MAX] {
        leaves.push((
            format!("item-{id}"),
            TyG::FnItem(FuncId::new(id)),
            Ty::FnItem(FuncId::new(id)),
        ));
    }
    // Invalid physical geometry is still real, serde-representable type data.
    // Substitution must preserve it; layout/use validation remains separate.
    for (size, align) in [(0, 1), (8, 8), (0, 0), (3, 2), (u64::MAX, 1), (1, u64::MAX)] {
        let layout = StorageLayout::new(size, align);
        leaves.push((
            format!("storage-{size}-{align}"),
            TyG::Storage(layout),
            Ty::Storage(layout),
        ));
    }
    let mut cases = Vec::new();
    for (label, source, value) in leaves {
        cases.push(checked(
            format!("{label}/leaf"),
            source.clone(),
            vec![],
            vec![],
            Some(value.clone()),
        ));
        cases.push(checked(
            format!("{label}/tuple"),
            TyG::Tuple(vec![source.clone(), TyG::U32]),
            vec![],
            vec![],
            Some(Ty::Tuple(vec![value.clone(), Ty::U32])),
        ));
        cases.push(checked(
            format!("{label}/nested-vector-ref"),
            TyG::Ref(Box::new(TyG::Vector(Box::new(source.clone()), 2))),
            vec![],
            vec![],
            Some(Ty::Ref(Box::new(Ty::Vector(Box::new(value.clone()), 2)))),
        ));
        cases.push(checked(
            format!("{label}/pointer-rc"),
            TyG::PtrConst(Box::new(TyG::Rc(Box::new(source)))),
            vec![],
            vec![],
            Some(Ty::PtrConst(Box::new(Ty::Rc(Box::new(value.clone()))))),
        ));
        cases.push(checked(
            format!("{label}/parameter-image"),
            TyG::Ext(TemplateRef::Param(ParamId::new(1))),
            vec![None, Some(value.clone())],
            vec![],
            Some(value.clone()),
        ));
        cases.push(checked(
            format!("{label}/hole-image"),
            TyG::Ext(TemplateRef::Hole(HoleId::new(2))),
            vec![],
            vec![None, None, Some(value.clone())],
            Some(value.clone()),
        ));
        cases.push(checked(
            format!("{label}/mixed-substitution"),
            TyG::Tuple(vec![
                TyG::FnItem(FuncId::new(11)),
                TyG::Ext(TemplateRef::Param(ParamId::new(1))),
                TyG::Storage(StorageLayout::new(8, 8)),
                TyG::Ext(TemplateRef::Hole(HoleId::new(2))),
            ]),
            vec![None, Some(value.clone())],
            vec![None, None, Some(value.clone())],
            Some(Ty::Tuple(vec![
                Ty::FnItem(FuncId::new(11)),
                value.clone(),
                Ty::Storage(StorageLayout::new(8, 8)),
                value,
            ])),
        ));
    }
    cases.push(checked(
        "missing-parameter".into(),
        TyG::Ext(TemplateRef::Param(ParamId::new(0))),
        vec![],
        vec![],
        None,
    ));
    cases.push(checked(
        "missing-hole".into(),
        TyG::Ext(TemplateRef::Hole(HoleId::new(0))),
        vec![],
        vec![],
        None,
    ));
    cases.push(checked(
        "missing-nested-parameter".into(),
        TyG::Tuple(vec![
            TyG::FnItem(FuncId::new(11)),
            TyG::Ext(TemplateRef::Param(ParamId::new(0))),
        ]),
        vec![None],
        vec![],
        None,
    ));
    cases.push(checked(
        "missing-nested-hole".into(),
        TyG::Tuple(vec![
            TyG::Storage(StorageLayout::new(8, 8)),
            TyG::Ext(TemplateRef::Hole(HoleId::new(0))),
        ]),
        vec![],
        vec![None],
        None,
    ));
    let image = Ty::Tuple(vec![
        Ty::Storage(StorageLayout::new(u64::MAX, 1)),
        Ty::FnItem(FuncId::new(u32::MAX)),
    ]);
    cases.push(checked(
        "nested-parameter-image".into(),
        TyG::RefMut(Box::new(TyG::Ext(TemplateRef::Param(ParamId::new(0))))),
        vec![Some(image.clone())],
        vec![],
        Some(Ty::RefMut(Box::new(image))),
    ));
    let image = Ty::Vector(Box::new(Ty::FnItem(FuncId::new(53))), 4);
    cases.push(checked(
        "nested-hole-image".into(),
        TyG::Rc(Box::new(TyG::Ext(TemplateRef::Hole(HoleId::new(0))))),
        vec![],
        vec![Some(image.clone())],
        Some(Ty::Rc(Box::new(image))),
    ));
    for ids in [[11, 53], [53, 11]] {
        cases.push(checked(
            format!("ordered-items-{}-{}", ids[0], ids[1]),
            TyG::Tuple(ids.map(|id| TyG::FnItem(FuncId::new(id))).to_vec()),
            vec![],
            vec![],
            Some(Ty::Tuple(
                ids.map(|id| Ty::FnItem(FuncId::new(id))).to_vec(),
            )),
        ));
    }
    assert_eq!(
        cases.len(),
        85,
        "explicit additive population; original corpus is unchanged"
    );
    cases
}

fn invoke(exe: &Path, document: &Json, label: &str) -> Vec<Verdict> {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::var_os("TRUST_IR_ORACLE_EVIDENCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_TARGET_TMPDIR")).join("template-constructor-evidence")
        });
    std::fs::create_dir_all(&directory).expect("owned constructor evidence directory");
    let stem = format!(
        "template-constructors-{}-{}-{label}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    );
    let input = directory.join(format!("{stem}.request.json"));
    std::fs::write(&input, serde_json::to_vec(document).unwrap())
        .expect("write exact constructor request");
    let output = Command::new(exe)
        .arg(&input)
        .output()
        .expect("run actual canonical oracle");
    std::fs::write(
        directory.join(format!("{stem}.response.json")),
        &output.stdout,
    )
    .unwrap();
    std::fs::write(directory.join(format!("{stem}.stderr.txt")), &output.stderr).unwrap();
    assert!(
        output.status.success(),
        "{label}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let reply: Json = serde_json::from_slice(&output.stdout).expect("structured oracle reply");
    let rows = reply
        .as_array()
        .unwrap_or_else(|| panic!("{label}: oracle refused whole request: {reply}"));
    assert_eq!(
        rows.len(),
        document["template_subst"].as_array().unwrap().len()
    );
    for row in rows {
        let fields = row.as_object().expect("one structured verdict per case");
        assert_eq!(fields.len(), 1, "unexpected oracle verdict: {row}");
        let (tag, value) = fields.iter().next().unwrap();
        match tag.as_str() {
            "agree" => assert_eq!(value, &Json::Bool(true)),
            "mismatch" | "unsupported" | "error" => assert!(value.is_string()),
            _ => panic!("unrecognized oracle verdict: {row}"),
        }
    }
    rows.iter().map(verdict).collect()
}

#[test]
fn storage_and_function_items_preserve_nested_substitution_and_identity() {
    let checked = positive_cases();
    let names = checked
        .iter()
        .map(|c| &c.case.label)
        .collect::<BTreeSet<_>>();
    assert_eq!(names.len(), 85);
    for item in &checked {
        assert_eq!(
            rust_subst(&item.case),
            item.expected,
            "independent Rust result: {}",
            item.case.label
        );
    }
    assert_eq!(checked.iter().filter(|c| c.expected.is_none()).count(), 4);
    let cases = checked.into_iter().map(|c| c.case).collect::<Vec<_>>();
    let Some(exe) = oracle() else { return };
    let verdicts = invoke(exe, &request(&cases), "positive");
    let failures = cases
        .iter()
        .zip(&verdicts)
        .filter(|(_, v)| **v != Verdict::Agree)
        .map(|(c, v)| format!("{}: {v:?}", c.label))
        .collect::<Vec<_>>();
    assert!(
        failures.is_empty(),
        "new constructor population failed (no unsupported allowance): {failures:#?}"
    );
    eprintln!("template_constructor_coverage: positive=85 agree=85 missing_images=4 unsupported=0");

    let item = |id| TyG::FnItem(FuncId::new(id));
    let storage = |size, align| TyG::Storage(StorageLayout::new(size, align));
    let mut forged = Vec::new();
    for (index, (source, params, holes, wrong)) in [
        (item(11), vec![], vec![], Ty::FnItem(FuncId::new(53))),
        (item(11), vec![], vec![], Ty::Unit),
        (item(11), vec![], vec![], Ty::Func(FuncTyId::new(0))),
        (
            storage(8, 8),
            vec![],
            vec![],
            Ty::Storage(StorageLayout::new(16, 8)),
        ),
        (
            storage(8, 8),
            vec![],
            vec![],
            Ty::Storage(StorageLayout::new(8, 4)),
        ),
        (
            storage(0, 0),
            vec![],
            vec![],
            Ty::Storage(StorageLayout::new(0, 1)),
        ),
        (
            TyG::Tuple(vec![storage(8, 8), item(11)]),
            vec![],
            vec![],
            Ty::Tuple(vec![
                Ty::Storage(StorageLayout::new(8, 8)),
                Ty::FnItem(FuncId::new(53)),
            ]),
        ),
        (
            TyG::Tuple(vec![storage(8, 8), item(11)]),
            vec![],
            vec![],
            Ty::Tuple(vec![Ty::Unit, Ty::FnItem(FuncId::new(11))]),
        ),
        (
            TyG::Ext(TemplateRef::Param(ParamId::new(0))),
            vec![Some(Ty::FnItem(FuncId::new(11)))],
            vec![],
            Ty::FnItem(FuncId::new(53)),
        ),
        (
            TyG::Ext(TemplateRef::Hole(HoleId::new(0))),
            vec![],
            vec![Some(Ty::Storage(StorageLayout::new(8, 8)))],
            Ty::Storage(StorageLayout::new(8, 4)),
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let case = Case {
            label: format!("forged-{index}"),
            ty: source,
            params,
            holes,
        };
        assert_ne!(rust_subst(&case), Some(wrong.clone()));
        let mut row = request(&[case])["template_subst"][0].clone();
        row["expected"] = serde_json::to_value(wrong).unwrap();
        forged.push(row);
    }
    let verdicts = invoke(exe, &json!({"template_subst": forged}), "forged");
    assert!(
        verdicts.iter().all(|v| matches!(v, Verdict::Mismatch(_))),
        "forged identities/geometries must mismatch: {verdicts:?}"
    );
    assert_eq!(verdicts.len(), 10);
    eprintln!("template_constructor_coverage: forged=10 mismatches=10");

    // Derived serde also accepts sequence-form structs and ignores unknown
    // object fields. Check those real input shapes, including image decoding,
    // rather than misclassifying an accepted Rust shape as malformed.
    let accepted_shapes = [
        (
            json!({"Storage": [8, 8]}),
            vec![],
            vec![],
            Ty::Storage(StorageLayout::new(8, 8)),
        ),
        (
            json!({"Storage": [u64::MAX, 1]}),
            vec![],
            vec![],
            Ty::Storage(StorageLayout::new(u64::MAX, 1)),
        ),
        (
            json!({"Storage": {"size_bytes": 0, "align_bytes": 0, "unused": 53}}),
            vec![],
            vec![],
            Ty::Storage(StorageLayout::new(0, 0)),
        ),
        (
            json!({"Tuple": [{"FnItem": 11}, {"Storage": [0, 1]}]}),
            vec![],
            vec![],
            Ty::Tuple(vec![
                Ty::FnItem(FuncId::new(11)),
                Ty::Storage(StorageLayout::new(0, 1)),
            ]),
        ),
        (
            json!({"Ext": {"Param": 0}}),
            vec![json!({"Storage": [8, 8]})],
            vec![],
            Ty::Storage(StorageLayout::new(8, 8)),
        ),
        (
            json!({"Ext": {"Hole": 0}}),
            vec![],
            vec![json!({"Storage": {"size_bytes": 1, "align_bytes": u64::MAX,
                                  "unused": {"FnItem": 53}}})],
            Ty::Storage(StorageLayout::new(1, u64::MAX)),
        ),
    ];
    let rows = accepted_shapes
        .into_iter()
        .enumerate()
        .map(|(index, (ty, params, holes, expected))| {
            let case = Case {
                label: format!("serde-shape-{index}"),
                ty: serde_json::from_value(ty.clone()).expect("real template serde shape"),
                params: params
                    .iter()
                    .map(|image| Some(serde_json::from_value(image.clone()).unwrap()))
                    .collect(),
                holes: holes
                    .iter()
                    .map(|image| Some(serde_json::from_value(image.clone()).unwrap()))
                    .collect(),
            };
            assert_eq!(rust_subst(&case), Some(expected.clone()), "{}", case.label);
            json!({"ty": ty, "params": params, "holes": holes, "expected": expected})
        })
        .collect::<Vec<_>>();
    let verdicts = invoke(exe, &json!({"template_subst": rows}), "serde-shapes");
    assert!(
        verdicts.iter().all(|v| *v == Verdict::Agree),
        "accepted Rust shapes must agree without normalization: {verdicts:?}"
    );
    assert_eq!(verdicts.len(), 6);
    eprintln!("template_constructor_coverage: serde_shapes=6 agree=6 unsupported=0");

    let overflow = Json::Number(serde_json::Number::from_f64(2_f64.powi(64)).unwrap());
    let malformed = [
        json!({"FnItem": u64::from(u32::MAX) + 1}),
        json!({"FnItem": -1}),
        json!({"FnItem": "11"}),
        json!({"Storage": {"size_bytes": overflow, "align_bytes": 1}}),
        json!({"Storage": {"size_bytes": 0, "align_bytes": overflow}}),
        json!({"Storage": {"size_bytes": -1, "align_bytes": 1}}),
        json!({"Storage": {"size_bytes": 8}}),
        json!({"Storage": [8]}),
        json!({"Storage": {"size_bytes": "8", "align_bytes": 8}}),
        json!({"Storage": {"size_bytes": 8, "align_bytes": null}}),
        json!({"Storage": [8, 8, 8]}),
        json!({"Storage": [8, "8"]}),
        json!({"Storage": [-1, 8]}),
        json!({"Storage": [overflow, 8]}),
    ];
    let rows = malformed
        .into_iter()
        .map(|ty| {
            assert!(
                serde_json::from_value::<Ty>(ty.clone()).is_err(),
                "the real Rust shape must refuse {ty}"
            );
            json!({"ty": ty, "params": [], "holes": [], "expected": null})
        })
        .collect::<Vec<_>>();
    let verdicts = invoke(exe, &json!({"template_subst": rows}), "malformed");
    assert!(
        verdicts.iter().all(|v| matches!(v, Verdict::Error(_))),
        "malformed real serde shapes must remain errors: {verdicts:?}"
    );
    assert_eq!(verdicts.len(), 14);
    eprintln!("template_constructor_coverage: malformed=14 errors=14");
}
