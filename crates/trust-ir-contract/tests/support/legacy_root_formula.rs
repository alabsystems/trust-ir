//! Test-only preserved Root54b grammar, independent of the replacement fold.
#![allow(dead_code)]
use serde_json::{Map, Value};
use std::collections::BTreeMap;
use std::fmt::Write as _;
const TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION: &str = "trust_wp.trust-formula.v1";
pub fn accepts(value: &Value) -> bool {
    validate_arithmetic_free_trust_formula_v1(value).is_ok()
}
fn validate_arithmetic_free_trust_formula_v1(value: &Value) -> Result<(), String> {
    let object = value.as_object().ok_or_else(|| {
        format!("typed `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}` predicate must be a JSON object")
    })?;
    reject_unknown_fields(object, "claim", &["schema", "variables", "result", "body"])?;

    match object.get("schema") {
        Some(Value::String(schema)) if schema == TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION => {}
        Some(Value::String(schema)) => {
            return Err(format!(
                "typed TrustFormulaV1 predicate uses schema `{schema}`, expected `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}`"
            ));
        }
        Some(_) => {
            return Err("typed TrustFormulaV1 predicate field `schema` must be a string".into());
        }
        None => {
            return Err(format!(
                "typed TrustFormulaV1 predicate is missing required field `schema`; expected `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}`"
            ));
        }
    }

    let mut env: BTreeMap<&str, TrustFormulaV1Sort> = BTreeMap::new();
    let mut path = String::with_capacity(64);
    if let Some(variables) = object.get("variables") {
        let variables = variables
            .as_array()
            .ok_or_else(|| "TrustFormulaV1 `variables` must be an array".to_string())?;
        for (index, binding) in variables.iter().enumerate() {
            path.clear();
            let _ = write!(path, "variables[{index}]");
            let (name, sort) = validate_binding(binding, &path, false)?;
            if env.insert(name, sort).is_some() {
                return Err(format!("duplicate TrustFormulaV1 binding `{name}`"));
            }
        }
    }

    let result_name = if let Some(result) = object.get("result") {
        let (name, sort) = validate_binding(result, "result", true)?;
        if env.insert(name, sort).is_some() {
            return Err(format!("duplicate TrustFormulaV1 binding `{name}`"));
        }
        Some(name)
    } else {
        None
    };

    let body = object.get("body").ok_or_else(|| {
        "typed TrustFormulaV1 predicate is missing required field `body`".to_string()
    })?;
    path.clear();
    path.push_str("body");
    let body_sort = validate_arithmetic_free_expr(body, &mut env, result_name, &mut path)?;
    require_formula_sort(&body_sort, &TrustFormulaV1Sort::Bool, &path)?;
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TrustFormulaV1Sort {
    Bool,
    Int,
    Seq,
    Ref { mutable: bool, inner: Box<Self> },
    TypeParam(char),
}

fn validate_binding<'a>(
    value: &'a Value,
    path: &str,
    optional_name: bool,
) -> Result<(&'a str, TrustFormulaV1Sort), String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{path} must be an object"))?;
    reject_unknown_fields(object, path, &["name", "sort"])?;
    let name = match object.get("name") {
        Some(Value::String(name)) => name.as_str(),
        Some(_) => return Err(format!("{path}.name must be a string")),
        None if optional_name => "result",
        None => return Err(format!("{path} is missing required field `name`")),
    };
    validate_name(name, path, ".name")?;
    let sort = object
        .get("sort")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{path}.sort must be a string"))?;
    let sort = decode_trust_formula_v1_sort(sort, path, ".sort")?;
    Ok((name, sort))
}

fn validate_child_expr<'a>(
    value: &'a Value,
    env: &mut BTreeMap<&'a str, TrustFormulaV1Sort>,
    result_name: Option<&str>,
    path: &mut String,
    suffix: &str,
    expected_sort: Option<&TrustFormulaV1Sort>,
) -> Result<TrustFormulaV1Sort, String> {
    let len = path.len();
    path.push_str(suffix);
    let result = validate_arithmetic_free_expr(value, env, result_name, path).and_then(|sort| {
        if let Some(expected) = expected_sort {
            require_formula_sort(&sort, expected, path)?;
        }
        Ok(sort)
    });
    path.truncate(len);
    result
}

fn validate_arithmetic_free_expr<'a>(
    value: &'a Value,
    env: &mut BTreeMap<&'a str, TrustFormulaV1Sort>,
    result_name: Option<&str>,
    path: &mut String,
) -> Result<TrustFormulaV1Sort, String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{path} must be an object"))?;

    if let Some(value) = object.get("bool") {
        reject_unknown_fields(object, path, &["bool"])?;
        return value
            .as_bool()
            .map(|_| TrustFormulaV1Sort::Bool)
            .ok_or_else(|| format!("{path}.bool must be a boolean"));
    }
    if let Some(value) = object.get("int") {
        reject_unknown_fields(object, path, &["int"])?;
        return value
            .as_i64()
            .map(|_| ())
            .or_else(|| value.as_u64().map(|_| ()))
            .map(|_| TrustFormulaV1Sort::Int)
            .ok_or_else(|| {
                format!("{path}.int must be an exact signed or unsigned 64-bit integer")
            });
    }
    if let Some(value) = object.get("var") {
        reject_unknown_fields(object, path, &["var"])?;
        let name = value
            .as_str()
            .ok_or_else(|| format!("{path}.var must be a string"))?;
        return env
            .get(name)
            .cloned()
            .ok_or_else(|| format!("{path}.var references undeclared binding `{name}`"));
    }
    if let Some(value) = object.get("result") {
        reject_unknown_fields(object, path, &["result"])?;
        if value.as_bool() != Some(true) {
            return Err(format!("{path}.result must be boolean true"));
        }
        let name = result_name
            .ok_or_else(|| format!("{path}.result requires a top-level result binding"))?;
        return env.get(name).cloned().ok_or_else(|| {
            format!("{path}.result references missing top-level result binding `{name}`")
        });
    }
    if let Some(inner) = object.get("old") {
        reject_unknown_fields(object, path, &["old"])?;
        return validate_child_expr(inner, env, result_name, path, ".old", None);
    }

    let op = object
        .get("op")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{path}.op must be a string"))?;
    if let Some(label) = arithmetic_op_label(op) {
        return Err(trust_formula_v1_arithmetic_refusal(label));
    }

    match op {
        "not" => {
            reject_unknown_fields(object, path, &["op", "expr"])?;
            let expr = object
                .get("expr")
                .ok_or_else(|| format!("{path}.expr is required"))?;
            validate_child_expr(
                expr,
                env,
                result_name,
                path,
                ".expr",
                Some(&TrustFormulaV1Sort::Bool),
            )?;
            Ok(TrustFormulaV1Sort::Bool)
        }
        "let" => {
            reject_unknown_fields(object, path, &["op", "name", "sort", "value", "body"])?;
            let (name, declared_sort) = required_name_and_sort(object, path)?;
            if env.contains_key(name) {
                return Err(format!("{path}.name shadows existing binding `{name}`"));
            }
            let value = object
                .get("value")
                .ok_or_else(|| format!("{path}.value is required"))?;
            validate_child_expr(
                value,
                env,
                result_name,
                path,
                ".value",
                Some(&declared_sort),
            )?;
            let body = object
                .get("body")
                .ok_or_else(|| format!("{path}.body is required"))?;
            env.insert(name, declared_sort);
            let result = validate_child_expr(body, env, result_name, path, ".body", None);
            env.remove(name);
            result
        }
        "forall" | "exists" => {
            reject_unknown_fields(object, path, &["op", "name", "sort", "body"])?;
            let (name, declared_sort) = required_name_and_sort(object, path)?;
            if env.contains_key(name) {
                return Err(format!("{path}.name shadows existing binding `{name}`"));
            }
            let body = object
                .get("body")
                .ok_or_else(|| format!("{path}.body is required"))?;
            env.insert(name, declared_sort);
            let result = validate_child_expr(
                body,
                env,
                result_name,
                path,
                ".body",
                Some(&TrustFormulaV1Sort::Bool),
            );
            env.remove(name);
            result?;
            Ok(TrustFormulaV1Sort::Bool)
        }
        "eq" | "ne" => {
            reject_unknown_fields(object, path, &["op", "lhs", "rhs"])?;
            let lhs = object
                .get("lhs")
                .ok_or_else(|| format!("{path}.lhs is required"))?;
            let rhs = object
                .get("rhs")
                .ok_or_else(|| format!("{path}.rhs is required"))?;
            let lhs_sort = validate_child_expr(lhs, env, result_name, path, ".lhs", None)?;
            // Equality is the sole operation retained for downstream
            // Seq/ref/type-parameter sorts; both sides must still agree.
            validate_child_expr(rhs, env, result_name, path, ".rhs", Some(&lhs_sort))?;
            // The downstream native-sort inference has no general Seq
            // sort. It accepts Seq equality only through its structural
            // reflexivity escape hatch (`lhs == rhs`), so mirror that
            // exact restriction here instead of admitting a claim that
            // the advertised common ingress later demotes.
            if lhs_sort == TrustFormulaV1Sort::Seq && lhs != rhs {
                return Err(format!(
                    "{path} compares distinct Seq expressions; native TrustFormulaV1 replay supports only structurally reflexive Seq equality"
                ));
            }
            Ok(TrustFormulaV1Sort::Bool)
        }
        "lt" | "le" | "gt" | "ge" => {
            reject_unknown_fields(object, path, &["op", "lhs", "rhs"])?;
            let lhs = object
                .get("lhs")
                .ok_or_else(|| format!("{path}.lhs is required"))?;
            let rhs = object
                .get("rhs")
                .ok_or_else(|| format!("{path}.rhs is required"))?;
            let lhs_sort = validate_child_expr(lhs, env, result_name, path, ".lhs", None)?;
            let rhs_sort = validate_child_expr(rhs, env, result_name, path, ".rhs", None)?;
            require_formula_sort_with_suffix(&lhs_sort, &TrustFormulaV1Sort::Int, path, ".lhs")?;
            require_formula_sort_with_suffix(&rhs_sort, &TrustFormulaV1Sort::Int, path, ".rhs")?;
            Ok(TrustFormulaV1Sort::Bool)
        }
        "and" | "or" | "implies" => {
            reject_unknown_fields(object, path, &["op", "lhs", "rhs"])?;
            let lhs = object
                .get("lhs")
                .ok_or_else(|| format!("{path}.lhs is required"))?;
            let rhs = object
                .get("rhs")
                .ok_or_else(|| format!("{path}.rhs is required"))?;
            let lhs_sort = validate_child_expr(lhs, env, result_name, path, ".lhs", None)?;
            let rhs_sort = validate_child_expr(rhs, env, result_name, path, ".rhs", None)?;
            require_formula_sort_with_suffix(&lhs_sort, &TrustFormulaV1Sort::Bool, path, ".lhs")?;
            require_formula_sort_with_suffix(&rhs_sort, &TrustFormulaV1Sort::Bool, path, ".rhs")?;
            Ok(TrustFormulaV1Sort::Bool)
        }
        unsupported => Err(format!(
            "{path}.op `{unsupported}` is outside the arithmetic-free TrustFormulaV1 fragment"
        )),
    }
}

fn required_name_and_sort<'a>(
    object: &'a Map<String, Value>,
    path: &str,
) -> Result<(&'a str, TrustFormulaV1Sort), String> {
    let name = object
        .get("name")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{path}.name must be a string"))?;
    validate_name(name, path, ".name")?;
    let sort = object
        .get("sort")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{path}.sort must be a string"))?;
    let sort = decode_trust_formula_v1_sort(sort, path, ".sort")?;
    Ok((name, sort))
}

fn decode_trust_formula_v1_sort(
    sort: &str,
    path: &str,
    suffix: &str,
) -> Result<TrustFormulaV1Sort, String> {
    let sort = sort.trim();
    if let Some(inner) = sort.strip_prefix("&mut ") {
        return Ok(TrustFormulaV1Sort::Ref {
            mutable: true,
            inner: Box::new(decode_trust_formula_v1_sort(inner, path, suffix)?),
        });
    }
    if let Some(inner) = sort.strip_prefix('&') {
        return Ok(TrustFormulaV1Sort::Ref {
            mutable: false,
            inner: Box::new(decode_trust_formula_v1_sort(inner, path, suffix)?),
        });
    }
    if sort.starts_with('[') && sort.ends_with(']') {
        let inner = sort[1..sort.len() - 1].trim();
        if inner.is_empty() {
            return Err(format!("{path}{suffix} slice element type is empty"));
        }
        let _ = decode_trust_formula_v1_sort(inner, path, suffix)?;
        return Ok(TrustFormulaV1Sort::Seq);
    }
    match sort {
        "int" | "Int" => Ok(TrustFormulaV1Sort::Int),
        "bool" | "Bool" => Ok(TrustFormulaV1Sort::Bool),
        "seq" | "Seq" => Ok(TrustFormulaV1Sort::Seq),
        _ => {
            let mut chars = sort.chars();
            if let (Some(ch), None) = (chars.next(), chars.next())
                && ch.is_ascii_uppercase()
            {
                return Ok(TrustFormulaV1Sort::TypeParam(ch));
            }
            Err(format!(
                "{path}{suffix} `{sort}` is outside the TrustFormulaV1 sort fragment"
            ))
        }
    }
}

fn require_formula_sort(
    actual: &TrustFormulaV1Sort,
    expected: &TrustFormulaV1Sort,
    path: &str,
) -> Result<(), String> {
    require_formula_sort_with_suffix(actual, expected, path, "")
}

fn require_formula_sort_with_suffix(
    actual: &TrustFormulaV1Sort,
    expected: &TrustFormulaV1Sort,
    path: &str,
    suffix: &str,
) -> Result<(), String> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!(
            "{path}{suffix} has sort {actual:?}, expected {expected:?} in TrustFormulaV1"
        ))
    }
}

fn validate_name(name: &str, path: &str, suffix: &str) -> Result<(), String> {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return Err(format!("{path}{suffix} is empty"));
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return Err(format!(
            "{path}{suffix} must start with `_` or an ASCII letter"
        ));
    }
    if !chars.all(|ch| {
        ch == '_'
            || ch.is_ascii_alphanumeric()
            || matches!(ch, '#' | '.' | '[' | ']' | '*' | '@' | '-' | ';' | '=')
    }) {
        return Err(format!(
            "{path}{suffix} contains characters outside the supported SMT-symbol set"
        ));
    }
    Ok(())
}

fn reject_unknown_fields(
    object: &Map<String, Value>,
    path: &str,
    allowed: &[&str],
) -> Result<(), String> {
    if let Some(field) = object
        .keys()
        .find(|field| !allowed.contains(&field.as_str()))
    {
        return Err(format!("{path} contains unsupported field `{field}`"));
    }
    Ok(())
}

fn arithmetic_op_label(op: &str) -> Option<&'static str> {
    match op {
        "add" | "+" => Some("add"),
        "sub" | "-" => Some("sub"),
        "mul" | "*" => Some("mul"),
        "div" | "/" => Some("div"),
        "mod" | "rem" | "%" => Some("mod"),
        "neg" => Some("neg"),
        _ => None,
    }
}

fn trust_wp_pure_expr_v1_arithmetic_refusal(op: &str) -> String {
    format!(
        "TrustWpPureExprV1 arithmetic operator `{op}` is outside the trust-wp stable-text bare-claim fragment: machine arithmetic modeled over unbounded Int is a false-proof vector (`x + 1 > x` is Int-provable but false at u64::MAX); see 2026-07-17 trust-wp lowering blueprint amendment 1"
    )
}

fn trust_formula_v1_arithmetic_refusal(op: &str) -> String {
    format!(
        "Formula arithmetic operator `{op}` is outside the trust_wp.trust-formula.v1 arithmetic-free fragment: machine arithmetic modeled over unbounded Int is a false-proof vector (`result + 1 > result` is Int-provable but false at u64::MAX); see 2026-07-17 trust-wp lowering blueprint amendment 1"
    )
}
