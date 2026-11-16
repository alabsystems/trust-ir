#![cfg(feature = "proof-json")]

//! The replacement fold is held against the two original independent wire
//! readers. The old readers live only in test fixtures, never in the library.

use std::sync::Arc;

use serde_json::{Value, json};
use trust_ir_contract::proof_json::UniqueJsonValue;
use trust_ir_contract::trust_formula_v1::{
    Algebra, BinaryOp, DecodePolicy, IntegerLiteral, Quantifier, UnaryOp, WireSort, decode_value,
    validate_value,
};

#[path = "support/legacy_json_depth.rs"]
mod compiler_json;
#[path = "support/legacy_root_formula_v1.rs"]
mod legacy_root;
#[path = "support/legacy_wp_formula_v1.rs"]
mod legacy_wp;
#[path = "support/legacy_native_json.rs"]
mod native_json;

fn wp_sort(sort: &WireSort) -> legacy_wp::ExprSort {
    use legacy_wp::ExprSort as S;
    match sort {
        WireSort::Bool => S::Bool,
        WireSort::Int => S::Int,
        WireSort::Seq => S::Seq,
        WireSort::Ref {
            mutable: false,
            inner,
        } => S::Ref(Box::new(wp_sort(inner))),
        WireSort::Ref {
            mutable: true,
            inner,
        } => S::MutRef(Box::new(wp_sort(inner))),
        WireSort::TypeParam(name) => S::TypeParam(*name),
    }
}

struct OriginalExpressionAlgebra;
impl Algebra for OriginalExpressionAlgebra {
    type Expr = legacy_wp::PureExpr;
    fn bool_literal(&mut self, value: bool) -> Self::Expr {
        Self::Expr::Bool(value)
    }
    fn integer_literal(&mut self, value: IntegerLiteral) -> Self::Expr {
        match value {
            IntegerLiteral::I64(value) => Self::Expr::Int(value),
            IntegerLiteral::U64(value) => legacy_wp::unsigned_literal_expr(value),
        }
    }
    fn variable(&mut self, name: &str, sort: &WireSort) -> Self::Expr {
        Self::Expr::Var(name.to_owned(), Some(wp_sort(sort)))
    }
    fn old(&mut self, inner: Self::Expr) -> Self::Expr {
        Self::Expr::Old(Arc::new(inner))
    }
    fn unary(&mut self, op: UnaryOp, inner: Self::Expr) -> Self::Expr {
        Self::Expr::UnOp(
            match op {
                UnaryOp::Not => legacy_wp::UnOp::Not,
                UnaryOp::Neg => legacy_wp::UnOp::Neg,
            },
            Arc::new(inner),
        )
    }
    fn binary(&mut self, op: BinaryOp, lhs: Self::Expr, rhs: Self::Expr) -> Self::Expr {
        use legacy_wp::BinOp as B;
        let op = match op {
            BinaryOp::Add => B::Add,
            BinaryOp::Sub => B::Sub,
            BinaryOp::Mul => B::Mul,
            BinaryOp::Div => B::Div,
            BinaryOp::Mod => B::Mod,
            BinaryOp::Eq => B::Eq,
            BinaryOp::Ne => B::Ne,
            BinaryOp::Lt => B::Lt,
            BinaryOp::Le => B::Le,
            BinaryOp::Gt => B::Gt,
            BinaryOp::Ge => B::Ge,
            BinaryOp::And => B::And,
            BinaryOp::Or => B::Or,
            BinaryOp::Implies => B::Implies,
        };
        Self::Expr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }
    fn let_binding(
        &mut self,
        name: &str,
        _: &WireSort,
        value: Self::Expr,
        body: Self::Expr,
    ) -> Self::Expr {
        Self::Expr::Let {
            var: name.to_owned(),
            value: Arc::new(value),
            body: Arc::new(body),
        }
    }
    fn quantified(
        &mut self,
        kind: Quantifier,
        name: &str,
        sort: &WireSort,
        body: Self::Expr,
    ) -> Self::Expr {
        match kind {
            Quantifier::Forall => Self::Expr::Forall {
                var: name.to_owned(),
                var_sort: Some(wp_sort(sort)),
                body: Arc::new(body),
                triggers: vec![],
            },
            Quantifier::Exists => Self::Expr::Exists {
                var: name.to_owned(),
                var_sort: Some(wp_sort(sort)),
                body: Arc::new(body),
                triggers: vec![],
            },
        }
    }
}

fn claim(body: Value) -> Value {
    json!({
        "schema": "trust_wp.trust-formula.v1",
        "variables": [
            {"name":"x","sort":"Int"}, {"name":"y","sort":"Bool"},
            {"name":"s","sort":"Seq"}, {"name":"t","sort":"T"},
            {"name":"p","sort":"&mut [Bool]"}
        ],
        "result": {"sort":"Int"},
        "body": body
    })
}

fn compare_original_readers(value: &Value) {
    let before = value.clone();
    let root = validate_value(value, DecodePolicy::CanonicalArithmeticFree);
    assert_eq!(
        root.is_ok(),
        legacy_root::accepts(value),
        "Root policy drift: {value}: {root:?}"
    );
    let old = legacy_wp::decode_value(value);
    let new = decode_value(
        value,
        DecodePolicy::NativeReplay,
        &mut OriginalExpressionAlgebra,
    );
    assert_eq!(
        new.is_ok(),
        old.is_ok(),
        "WP policy drift: {value}: old={old:?}, new={new:?}"
    );
    if let (Ok(old), Ok(new)) = (old, new) {
        assert_eq!(new.body, old.body, "WP expression changed: {value}");
        assert_eq!(
            new.declarations
                .iter()
                .map(|(name, sort)| (name.clone(), wp_sort(sort)))
                .collect::<Vec<_>>(),
            old.declarations,
            "declarations changed: {value}"
        );
    }
    assert_eq!(*value, before, "the decoder changed its original value");
}

#[test]
fn shared_fold_matches_both_original_grammars_and_constructed_expressions() {
    let atoms = [
        json!({"bool":true}),
        json!({"bool":false}),
        json!({"int":-1}),
        json!({"int":0}),
        json!({"int":i64::MIN}),
        json!({"int":i64::MAX}),
        json!({"int":u64::MAX}),
        json!({"var":"x"}),
        json!({"var":"y"}),
        json!({"var":"s"}),
        json!({"var":"t"}),
        json!({"var":"p"}),
        json!({"result":true}),
        json!({"var":"missing"}),
        json!({"int":1.5}),
    ];
    for atom in &atoms {
        compare_original_readers(&claim(atom.clone()));
        compare_original_readers(&claim(json!({"old": atom})));
        for unary in ["not", "neg", "foreign"] {
            compare_original_readers(&claim(json!({"op":unary,"expr":atom})));
        }
        for sort in ["int", "Bool", "Seq", "&Int", "&mut T", "T", "[]", "Foreign"] {
            for op in ["let", "forall", "exists"] {
                let mut body = json!({"op":op,"name":"bound","sort":sort,"body":atom});
                if op == "let" {
                    body["value"] = atom.clone();
                }
                compare_original_readers(&claim(body));
            }
        }
    }
    for lhs in &atoms {
        for rhs in &atoms {
            for op in [
                "add", "sub", "mul", "div", "mod", "eq", "ne", "lt", "le", "gt", "ge", "and", "or",
                "implies", "+", "rem", "foreign",
            ] {
                compare_original_readers(&claim(json!({"op":op,"lhs":lhs,"rhs":rhs})));
            }
        }
    }
}

#[test]
fn bindings_schema_aliases_and_malformed_records_match_original_readers() {
    let valid = claim(json!({"op":"eq","lhs":{"result":true},"rhs":{"var":"x"}}));
    compare_original_readers(&valid);
    for schema in [
        "trust_wp.trust-formula.v1",
        "trust-wp.trust-formula.v1",
        "trust_wp.trust_formula.v1",
        "trust-wp.trust_formula.v1",
        "trust-wp.pure-expr.v1",
        "other",
    ] {
        let mut value = valid.clone();
        value["schema"] = json!(schema);
        compare_original_readers(&value);
    }
    for field in ["schema", "variables", "result", "body"] {
        let mut value = valid.clone();
        value.as_object_mut().expect("object").remove(field);
        compare_original_readers(&value);
        let mut value = valid.clone();
        value[field] = Value::Null;
        compare_original_readers(&value);
    }
    for value in [Value::Null, json!([]), json!("result > 0"), json!(42)] {
        compare_original_readers(&value);
    }
    for name in [
        "",
        "1bad",
        "x y",
        "_0#s0_0",
        "arr[_i]",
        "p@1[off;min=2]",
        "old",
        "let",
        "x;",
    ] {
        let value = json!({"schema":"trust_wp.trust-formula.v1","variables":[{"name":name,"sort":"bool"}],"body":{"var":name}});
        compare_original_readers(&value);
    }
    for body in [
        json!({"op":"let","name":"x","sort":"Int","value":{"int":1},"body":{"var":"x"}}),
        json!({"op":"forall","name":"x","sort":"Int","body":{"bool":true}}),
        json!({"op":"let","name":"z","sort":"Bool","value":{"int":1},"body":{"var":"z"}}),
        json!({"op":"let","name":"z","sort":"Int","value":{"var":"z"},"body":{"bool":true}}),
        json!({"op":"and","lhs":{"op":"let","name":"z","sort":"Bool","value":{"bool":true},"body":{"var":"z"}},"rhs":{"var":"z"}}),
        json!({"bool":true,"int":0}),
        json!({"result":false}),
        json!({"op":"not","expr":{"bool":true},"extra":0}),
    ] {
        compare_original_readers(&claim(body));
    }
    let mut duplicate = valid;
    duplicate["variables"]
        .as_array_mut()
        .expect("array")
        .push(json!({"name":"result","sort":"Int"}));
    compare_original_readers(&duplicate);
}

#[test]
fn result_defaults_and_old_let_quantifier_meanings_are_preserved() {
    let value = json!({"schema":"trust_wp.trust-formula.v1","variables":[{"name":"a","sort":"Bool"}],"result":{"sort":"Bool"},"body":{"op":"let","name":"saved","sort":"Bool","value":{"old":{"result":true}},"body":{"op":"forall","name":"q","sort":"Bool","body":{"op":"eq","lhs":{"var":"saved"},"rhs":{"var":"q"}}}}});
    compare_original_readers(&value);
    let decoded = decode_value(
        &value,
        DecodePolicy::NativeReplay,
        &mut OriginalExpressionAlgebra,
    )
    .expect("claim");
    assert_eq!(decoded.result_name.as_deref(), Some("result"));
    assert_eq!(
        decoded.declarations,
        vec![
            ("a".into(), WireSort::Bool),
            ("result".into(), WireSort::Bool)
        ]
    );
    assert_eq!(decoded.body_sort, WireSort::Bool);
    assert!(
        matches!(decoded.body, legacy_wp::PureExpr::Let { value, .. } if matches!(&*value, legacy_wp::PureExpr::Old(_)))
    );
}

#[test]
fn exact_u64_boundary_and_native_legacy_typing_are_not_reinterpreted() {
    for literal in [
        json!(i64::MIN),
        json!(i64::MAX),
        json!(1_u64 << 63),
        json!(u64::MAX),
    ] {
        compare_original_readers(&claim(json!({"int":literal})));
    }
    let legacy = claim(json!({"op":"not","expr":{"int":1}}));
    assert!(validate_value(&legacy, DecodePolicy::NativeReplay).is_ok());
    assert!(validate_value(&legacy, DecodePolicy::CanonicalArithmeticFree).is_err());
    let integer_root = claim(json!({"int":1}));
    assert_eq!(
        validate_value(&integer_root, DecodePolicy::NativeReplay)
            .expect("legacy syntax")
            .body_sort,
        WireSort::Int
    );
    assert!(validate_value(&integer_root, DecodePolicy::CanonicalArithmeticFree).is_err());
    let false_claim = claim(json!({"bool":false}));
    let parsed = decode_value(
        &false_claim,
        DecodePolicy::NativeReplay,
        &mut OriginalExpressionAlgebra,
    )
    .expect("false is data, not a proof");
    assert_eq!(parsed.body, legacy_wp::PureExpr::Bool(false));
    for op in ["add", "sub", "mul", "div", "mod", "neg"] {
        let body = if op == "neg" {
            json!({"op":op,"expr":{"int":1}})
        } else {
            json!({"op":op,"lhs":{"int":1},"rhs":{"int":1}})
        };
        assert!(
            validate_value(&claim(body), DecodePolicy::CanonicalArithmeticFree)
                .expect_err("machine arithmetic must not be laundered through Int")
                .to_string()
                .contains("false-proof vector")
        );
    }
}

#[test]
fn native_diagnostics_and_unmodeled_quantifier_refusals_remain() {
    assert_eq!(
        validate_value(&json!("source"), DecodePolicy::NativeReplay)
            .expect_err("object required")
            .to_string(),
        "claim payload must be a JSON object"
    );
    for sort in ["Seq", "T", "[Int]"] {
        let value = claim(json!({"op":"forall","name":"z","sort":sort,"body":{"bool":true}}));
        assert!(
            validate_value(&value, DecodePolicy::NativeReplay)
                .expect_err("unmodeled range")
                .to_string()
                .contains("quantifier sort native replay does not model")
        );
    }
    let value =
        claim(json!({"op":"let","name":"z","sort":"Bool","value":{"int":0},"body":{"var":"z"}}));
    let error = validate_value(&value, DecodePolicy::NativeReplay)
        .expect_err("let type mismatch")
        .to_string();
    assert!(
        error.contains("sort `Bool`") && error.contains("sort `Int`"),
        "{error}"
    );
    let value = claim(json!({"op":"foreign"}));
    assert!(
        validate_value(&value, DecodePolicy::NativeReplay)
            .expect_err("unknown op")
            .to_string()
            .contains("outside the trust-formula v1 native int/bool fragment")
    );
}

#[test]
fn unique_json_rejects_escaped_duplicates_nested_arrays_and_trailing_input() {
    for (payload, key) in [
        (r#"{"body":true,"body":false}"#, "body"),
        (r#"{"items":[{"op":"eq","op":"ne"}]}"#, "op"),
        (r#"{"a":1,"\u0061":2}"#, "a"),
        (r#"[{"\u006fp":1,"op":2}]"#, "op"),
    ] {
        let error = serde_json::from_str::<UniqueJsonValue>(payload)
            .err()
            .expect("duplicate refused");
        assert!(
            error
                .to_string()
                .contains(&format!("duplicate JSON object key `{key}`")),
            "{error}"
        );
    }
    for payload in ["{} {}", "true false", "[] trailing", "1e400"] {
        assert!(
            serde_json::from_str::<UniqueJsonValue>(payload).is_err(),
            "{payload}"
        );
        assert!(native_json::parse(payload).is_err(), "{payload}");
    }
    let raw = r#"{"literal":"[{}]\\\"", "array":[true,18446744073709551615,null]}"#;
    let raw_before = raw.to_owned();
    let value = serde_json::from_str::<UniqueJsonValue>(raw)
        .expect("one value")
        .into_value();
    assert_eq!(
        value,
        serde_json::from_str::<Value>(raw).expect("same interpretation")
    );
    assert_eq!(raw, raw_before);
}

fn nested_array(depth: usize) -> String {
    format!("{}0{}", "[".repeat(depth), "]".repeat(depth))
}
fn consume_nested(mut value: Value, depth: usize) {
    for _ in 0..depth {
        let Value::Array(mut children) = value else {
            panic!("lost an array level")
        };
        assert_eq!(children.len(), 1);
        value = children.pop().expect("one child");
    }
    assert_eq!(value, json!(0));
}

#[test]
fn shared_visitor_preserves_compiler4096_and_native260_entrypoint_budgets() {
    let native = nested_array(260);
    consume_nested(
        native_json::parse(&native).expect("original native maximum"),
        260,
    );
    assert!(
        native_json::parse(&nested_array(261))
            .expect_err("native bound")
            .contains("depth budget")
    );
    let compiler = nested_array(4096);
    let value = compiler_json::from_str_deep::<UniqueJsonValue>(&compiler)
        .expect("original bounded deep stack")
        .into_value();
    consume_nested(value, 4096);
    assert!(compiler_json::from_str_deep::<UniqueJsonValue>(&nested_array(4097)).is_err());
    assert!(native_json::parse(r#"{"quoted":"[[[[{{{{\\\""}"#).is_ok());
    let duplicate = format!("{}{{\"a\":1,\"a\":2}}{}", "[".repeat(256), "]".repeat(256));
    let error = compiler_json::from_str_deep::<UniqueJsonValue>(&duplicate)
        .err()
        .expect("deep duplicate refused");
    assert!(error.to_string().contains("duplicate JSON object key `a`"));
}
