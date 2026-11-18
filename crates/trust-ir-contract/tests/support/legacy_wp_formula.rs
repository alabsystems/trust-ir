//! Test-only preserved WP374 wire decoder before engine-definedness replay.
//! The original engine-definedness pass remains in WP, not in this leaf.
#![allow(dead_code)]
use serde_json::{Map, Value};
use std::{collections::HashMap, fmt, sync::Arc};
const TRUST_FORMULA_CLAIM_SCHEMA_VERSION: &str = "trust-wp.trust-formula.v1";
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustFormulaDecodeError {
    message: String,
}
impl TrustFormulaDecodeError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}
impl fmt::Display for TrustFormulaDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprSort {
    Int,
    Bool,
    Seq,
    Ref(Box<Self>),
    MutRef(Box<Self>),
    TypeParam(char),
}
impl fmt::Display for ExprSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => f.write_str("Int"),
            Self::Bool => f.write_str("Bool"),
            Self::Seq => f.write_str("Seq"),
            Self::Ref(i) => write!(f, "&{i}"),
            Self::MutRef(i) => write!(f, "&mut {i}"),
            Self::TypeParam(c) => write!(f, "TypeParam({c})"),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
    DivTrunc,
    RemTrunc,
    Shl,
    Shr,
    BitAnd,
    BitXor,
    BitOr,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
    BitNot,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PureExpr {
    Bool(bool),
    Int(i64),
    Var(String, Option<ExprSort>),
    Old(Arc<Self>),
    UnOp(UnOp, Arc<Self>),
    BinOp(Arc<Self>, BinOp, Arc<Self>),
    Let {
        var: String,
        value: Arc<Self>,
        body: Arc<Self>,
    },
    Forall {
        var: String,
        var_sort: Option<ExprSort>,
        body: Arc<Self>,
        triggers: Vec<()>,
    },
    Exists {
        var: String,
        var_sort: Option<ExprSort>,
        body: Arc<Self>,
        triggers: Vec<()>,
    },
    Other,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Claim {
    pub declarations: Vec<(String, ExprSort)>,
    pub body: PureExpr,
}
#[derive(Debug, Clone, PartialEq, Eq)]
struct Binding {
    name: String,
    sort: ExprSort,
}
fn intern_sort_name(name: &str) -> char {
    name.chars().next().expect("validated sort")
}
pub fn decode_value(value: &Value) -> Result<Claim, TrustFormulaDecodeError> {
    let value = value.clone();
    let object = value
        .as_object()
        .ok_or_else(|| TrustFormulaDecodeError::new("claim payload must be a JSON object"))?;
    reject_unknown_fields(object, "claim", &["schema", "variables", "result", "body"])?;

    let schema = required_str(object.get("schema"), "schema")?;
    // The compiler-side envelope tags the schema with the namespace token in its
    // identifier spelling (`trust_wp.trust-formula.v1`), while this constant uses
    // the crate spelling (`trust-wp.…`). They denote the same format, so compare
    // separator-canonically (only `_`↔`-` differs) — like the trust-mc identity
    // fix. Distinct schemas (e.g. `…pure-expr.v1`) still mismatch.
    if schema.replace('_', "-") != TRUST_FORMULA_CLAIM_SCHEMA_VERSION {
        return Err(TrustFormulaDecodeError::new(format!(
            "unsupported trust formula schema `{schema}`; expected `{TRUST_FORMULA_CLAIM_SCHEMA_VERSION}`"
        )));
    }

    let mut env: HashMap<String, ExprSort> = HashMap::new();
    let mut declarations = Vec::new();
    if let Some(variables) = object.get("variables") {
        let variables: &[Value] = variables
            .as_array()
            .map(Vec::as_slice)
            .ok_or_else(|| TrustFormulaDecodeError::new("variables must be an array"))?;
        for (index, variable) in variables.iter().enumerate() {
            let binding = decode_binding(variable, &format!("variables[{index}]"))?;
            declarations.push((binding.name.clone(), binding.sort.clone()));
            insert_binding(&mut env, binding)?;
        }
    }

    let result_name = if let Some(result) = object.get("result") {
        let binding = decode_result_binding(result)?;
        let result_name = binding.name.clone();
        declarations.push((binding.name.clone(), binding.sort.clone()));
        insert_binding(&mut env, binding)?;
        Some(result_name)
    } else {
        None
    };

    let body = object
        .get("body")
        .ok_or_else(|| TrustFormulaDecodeError::new("missing required field `body`"))?;
    let body = decode_expr(body, &env, result_name.as_deref(), "body")?;
    Ok(Claim { declarations, body })
}

fn decode_binding(value: &Value, path: &str) -> Result<Binding, TrustFormulaDecodeError> {
    let object = value
        .as_object()
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path} must be an object")))?;
    reject_unknown_fields(object, path, &["name", "sort"])?;
    let name = required_str(object.get("name"), &format!("{path}.name"))?;
    validate_name(name, &format!("{path}.name"))?;
    let sort = decode_sort(
        required_str(object.get("sort"), &format!("{path}.sort"))?,
        path,
    )?;
    Ok(Binding {
        name: name.to_string(),
        sort,
    })
}

fn decode_result_binding(value: &Value) -> Result<Binding, TrustFormulaDecodeError> {
    let object = value
        .as_object()
        .ok_or_else(|| TrustFormulaDecodeError::new("result must be an object"))?;
    reject_unknown_fields(object, "result", &["name", "sort"])?;
    let name = optional_str(object.get("name"), "result.name")?.unwrap_or("result");
    validate_name(name, "result.name")?;
    let sort = decode_sort(required_str(object.get("sort"), "result.sort")?, "result")?;
    Ok(Binding {
        name: name.to_string(),
        sort,
    })
}

fn insert_binding(
    env: &mut HashMap<String, ExprSort>,
    binding: Binding,
) -> Result<(), TrustFormulaDecodeError> {
    if env.insert(binding.name.clone(), binding.sort).is_some() {
        return Err(TrustFormulaDecodeError::new(format!(
            "duplicate binding `{}`",
            binding.name
        )));
    }
    Ok(())
}

fn decode_expr(
    value: &Value,
    env: &HashMap<String, ExprSort>,
    result_name: Option<&str>,
    path: &str,
) -> Result<PureExpr, TrustFormulaDecodeError> {
    let object = value
        .as_object()
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path} must be an object")))?;

    if let Some(value) = object.get("bool") {
        let value: &Value = value;
        reject_unknown_fields(object, path, &["bool"])?;
        return value
            .as_bool()
            .map(PureExpr::Bool)
            .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.bool must be a boolean")));
    }
    if let Some(value) = object.get("int") {
        let value: &Value = value;
        reject_unknown_fields(object, path, &["int"])?;
        return decode_int_literal(value, path);
    }
    if let Some(value) = object.get("var") {
        let value: &Value = value;
        reject_unknown_fields(object, path, &["var"])?;
        let name = value
            .as_str()
            .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.var must be a string")))?;
        let sort = env.get(name).cloned().ok_or_else(|| {
            TrustFormulaDecodeError::new(format!(
                "{path}.var references undeclared binding `{name}`"
            ))
        })?;
        return Ok(PureExpr::Var(name.to_string(), Some(sort)));
    }
    if let Some(value) = object.get("result") {
        let value: &Value = value;
        reject_unknown_fields(object, path, &["result"])?;
        let true_value = value.as_bool().ok_or_else(|| {
            TrustFormulaDecodeError::new(format!("{path}.result must be boolean true"))
        })?;
        if !true_value {
            return Err(TrustFormulaDecodeError::new(format!(
                "{path}.result must be boolean true"
            )));
        }
        let name = result_name.ok_or_else(|| {
            TrustFormulaDecodeError::new(format!(
                "{path}.result requires a top-level result binding"
            ))
        })?;
        let sort = env.get(name).cloned().ok_or_else(|| {
            TrustFormulaDecodeError::new("top-level result binding is missing from environment")
        })?;
        return Ok(PureExpr::Var(name.to_string(), Some(sort)));
    }
    if let Some(inner) = object.get("old") {
        reject_unknown_fields(object, path, &["old"])?;
        return Ok(PureExpr::Old(Arc::new(decode_expr(
            inner,
            env,
            result_name,
            &format!("{path}.old"),
        )?)));
    }

    let op = required_str(object.get("op"), &format!("{path}.op"))?;
    match op {
        "not" | "neg" => {
            reject_unknown_fields(object, path, &["op", "expr"])?;
            let expr = object
                .get("expr")
                .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.expr is required")))?;
            let op = if op == "not" { UnOp::Not } else { UnOp::Neg };
            Ok(PureExpr::UnOp(
                op,
                Arc::new(decode_expr(
                    expr,
                    env,
                    result_name,
                    &format!("{path}.expr"),
                )?),
            ))
        }
        "let" => decode_let_expr(object, env, result_name, path),
        "forall" | "exists" => decode_quantifier_expr(op, object, env, result_name, path),
        "add" | "sub" | "mul" | "div" | "mod" | "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "and"
        | "or" | "implies" => {
            reject_unknown_fields(object, path, &["op", "lhs", "rhs"])?;
            let lhs = object
                .get("lhs")
                .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.lhs is required")))?;
            let rhs = object
                .get("rhs")
                .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.rhs is required")))?;
            Ok(PureExpr::BinOp(
                Arc::new(decode_expr(lhs, env, result_name, &format!("{path}.lhs"))?),
                decode_bin_op(op),
                Arc::new(decode_expr(rhs, env, result_name, &format!("{path}.rhs"))?),
            ))
        }
        unsupported => Err(TrustFormulaDecodeError::new(format!(
            "{path}.op `{unsupported}` is outside the trust-formula v1 native int/bool fragment"
        ))),
    }
}

fn decode_int_literal(value: &Value, path: &str) -> Result<PureExpr, TrustFormulaDecodeError> {
    value
        .as_i64()
        .map(PureExpr::Int)
        .or_else(|| value.as_u64().map(unsigned_literal_expr))
        .ok_or_else(|| {
            TrustFormulaDecodeError::new(format!(
                "{path}.int must be an exact signed or unsigned 64-bit integer"
            ))
        })
}

fn decode_quantifier_expr(
    op: &str,
    object: &Map<String, Value>,
    env: &HashMap<String, ExprSort>,
    result_name: Option<&str>,
    path: &str,
) -> Result<PureExpr, TrustFormulaDecodeError> {
    reject_unknown_fields(object, path, &["op", "name", "sort", "body"])?;
    let name = required_str(object.get("name"), &format!("{path}.name"))?;
    validate_name(name, &format!("{path}.name"))?;
    if env.contains_key(name) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path}.name shadows existing binding `{name}`"
        )));
    }
    let written_sort = required_str(object.get("sort"), &format!("{path}.sort"))?;
    let sort = decode_sort(written_sort, path)?;
    // A binder ranges over its sort, and native replay models the range of
    // `int`, `bool` and a reference (a pointer) only: a type parameter could
    // be any type, a sequence is not an integer, and either was read as one.
    if !matches!(
        sort,
        ExprSort::Int | ExprSort::Bool | ExprSort::Ref(_) | ExprSort::MutRef(_)
    ) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path}.sort `{written_sort}` is a quantifier sort native replay does not model: a \
             binder ranges over `int`, `bool` or a reference"
        )));
    }
    let body = object
        .get("body")
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.body is required")))?;

    let mut scoped_env = env.clone();
    insert_binding(
        &mut scoped_env,
        Binding {
            name: name.to_string(),
            sort: sort.clone(),
        },
    )?;
    let body = Arc::new(decode_expr(
        body,
        &scoped_env,
        result_name,
        &format!("{path}.body"),
    )?);

    match op {
        "forall" => Ok(PureExpr::Forall {
            var: name.to_string(),
            var_sort: Some(sort),
            body,
            triggers: Vec::new(),
        }),
        "exists" => Ok(PureExpr::Exists {
            var: name.to_string(),
            var_sort: Some(sort),
            body,
            triggers: Vec::new(),
        }),
        _ => unreachable!("quantifier operator checked by caller"),
    }
}

fn decode_let_expr(
    object: &Map<String, Value>,
    env: &HashMap<String, ExprSort>,
    result_name: Option<&str>,
    path: &str,
) -> Result<PureExpr, TrustFormulaDecodeError> {
    reject_unknown_fields(object, path, &["op", "name", "sort", "value", "body"])?;
    let name = required_str(object.get("name"), &format!("{path}.name"))?;
    validate_name(name, &format!("{path}.name"))?;
    if env.contains_key(name) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path}.name shadows existing binding `{name}`"
        )));
    }
    let sort = decode_sort(
        required_str(object.get("sort"), &format!("{path}.sort"))?,
        path,
    )?;
    let value = object
        .get("value")
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.value is required")))?;
    let body = object
        .get("body")
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path}.body is required")))?;
    let value = decode_expr(value, env, result_name, &format!("{path}.value"))?;
    // The declaration types every read of the name in the body; the value is
    // what those reads denote. A value of another sort would be read at the
    // declared sort by the body and at its own by whatever inlines it.
    match decoded_sort(&value) {
        Some(value_sort) if value_sort == sort => {}
        found => {
            return Err(TrustFormulaDecodeError::new(format!(
                "{path} declares `{name}` at sort `{sort}` but binds it to a value of sort `{}`",
                found.map_or_else(|| "unknown".to_string(), |found| found.to_string())
            )));
        }
    }
    let mut scoped_env = env.clone();
    insert_binding(
        &mut scoped_env,
        Binding {
            name: name.to_string(),
            sort,
        },
    )?;
    Ok(PureExpr::Let {
        var: name.to_string(),
        value: Arc::new(value),
        body: Arc::new(decode_expr(
            body,
            &scoped_env,
            result_name,
            &format!("{path}.body"),
        )?),
    })
}

/// The sort of an expression this decoder produced: every name it emits
/// carries its declared sort, so the sort follows from the syntax. `None` for
/// a shape the decoder never emits.
fn decoded_sort(expr: &PureExpr) -> Option<ExprSort> {
    match expr {
        PureExpr::Bool(_) => Some(ExprSort::Bool),
        PureExpr::Int(_) => Some(ExprSort::Int),
        PureExpr::Var(_, sort) => sort.clone(),
        PureExpr::Old(inner) => decoded_sort(inner),
        PureExpr::Let { body, .. } => decoded_sort(body),
        PureExpr::UnOp(UnOp::Not, _) | PureExpr::Forall { .. } | PureExpr::Exists { .. } => {
            Some(ExprSort::Bool)
        }
        PureExpr::UnOp(UnOp::Neg | UnOp::BitNot, _) => Some(ExprSort::Int),
        PureExpr::BinOp(_, op, _) => Some(match op {
            BinOp::Eq
            | BinOp::Ne
            | BinOp::Lt
            | BinOp::Le
            | BinOp::Gt
            | BinOp::Ge
            | BinOp::And
            | BinOp::Or
            | BinOp::Implies => ExprSort::Bool,
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::DivTrunc
            | BinOp::RemTrunc
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::BitOr => ExprSort::Int,
        }),
        _ => None,
    }
}

fn decode_bin_op(op: &str) -> BinOp {
    match op {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        "div" => BinOp::Div,
        "mod" => BinOp::Mod,
        "eq" => BinOp::Eq,
        "ne" => BinOp::Ne,
        "lt" => BinOp::Lt,
        "le" => BinOp::Le,
        "gt" => BinOp::Gt,
        "ge" => BinOp::Ge,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "implies" => BinOp::Implies,
        _ => unreachable!("operator checked by caller"),
    }
}

fn decode_sort(sort: &str, path: &str) -> Result<ExprSort, TrustFormulaDecodeError> {
    let sort = sort.trim();
    if let Some(inner) = sort.strip_prefix("&mut ") {
        return Ok(ExprSort::MutRef(Box::new(decode_sort(inner, path)?)));
    }
    if let Some(inner) = sort.strip_prefix('&') {
        return Ok(ExprSort::Ref(Box::new(decode_sort(inner, path)?)));
    }
    if sort.starts_with('[') && sort.ends_with(']') {
        let inner = sort[1..sort.len() - 1].trim();
        if inner.is_empty() {
            return Err(TrustFormulaDecodeError::new(format!(
                "{path}.sort slice element type is empty"
            )));
        }
        let _ = decode_sort(inner, path)?;
        return Ok(ExprSort::Seq);
    }

    match sort {
        "int" | "Int" => Ok(ExprSort::Int),
        "bool" | "Bool" => Ok(ExprSort::Bool),
        "seq" | "Seq" => Ok(ExprSort::Seq),
        type_param if is_type_param_sort(type_param) => {
            Ok(ExprSort::TypeParam(intern_sort_name(type_param)))
        }
        unsupported => Err(TrustFormulaDecodeError::new(format!(
            "{path}.sort `{unsupported}` is outside the trust-formula v1 native replay sort fragment"
        ))),
    }
}

fn is_type_param_sort(sort: &str) -> bool {
    let mut chars = sort.chars();
    matches!(
        (chars.next(), chars.next()),
        (Some(ch), None) if ch.is_ascii_uppercase()
    )
}

fn required_str<'a>(
    value: Option<&'a Value>,
    path: &str,
) -> Result<&'a str, TrustFormulaDecodeError> {
    value
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("missing required field `{path}`")))?
        .as_str()
        .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path} must be a string")))
}

fn optional_str<'a>(
    value: Option<&'a Value>,
    path: &str,
) -> Result<Option<&'a str>, TrustFormulaDecodeError> {
    value
        .map(|value: &Value| {
            value
                .as_str()
                .ok_or_else(|| TrustFormulaDecodeError::new(format!("{path} must be a string")))
        })
        .transpose()
}

fn validate_name(name: &str, path: &str) -> Result<(), TrustFormulaDecodeError> {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return Err(TrustFormulaDecodeError::new(format!("{path} is empty")));
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path} must start with `_` or an ASCII letter"
        )));
    }
    // Accept the SMT-symbol characters the compiler's VC generator legitimately
    // emits in variable names: SSA version suffixes (`_0#s0_0`) and place
    // projections (`_t.0`, `arr[_i]`, `*p`, `@1`, `[off;min=2]`). These are
    // opaque keys in trust-wp's native pure replay (and quoted in any textual
    // SMT backend), and the bounds-obligation path already accepts them — so the
    // postcondition/refinement claim schema must too, rather than fail-closing a
    // legitimate name and reporting a contract `Unsupported`.
    if !chars.all(is_claim_name_char) {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path} contains characters outside the supported SMT-symbol set"
        )));
    }
    Ok(())
}

/// Characters permitted after the first in a `trust_wp.trust-formula.v1` variable
/// name: identifier characters plus the SSA-version (`#`) and place-projection
/// sigils (`.`, `[`, `]`, `*`, `@`, `-`, `;`, `=`) the trust-vcgen formula layer
/// produces. The leading character is still constrained to `_` or an ASCII
/// letter by the caller, matching every base local / source name.
fn is_claim_name_char(ch: char) -> bool {
    ch == '_'
        || ch.is_ascii_alphanumeric()
        || matches!(ch, '#' | '.' | '[' | ']' | '*' | '@' | '-' | ';' | '=')
}

fn reject_unknown_fields(
    object: &Map<String, Value>,
    path: &str,
    allowed: &[&str],
) -> Result<(), TrustFormulaDecodeError> {
    if let Some(field) = object
        .keys()
        .find(|field: &&String| !allowed.contains(&field.as_str()))
    {
        return Err(TrustFormulaDecodeError::new(format!(
            "{path} contains unsupported field `{field}`"
        )));
    }
    Ok(())
}

pub fn unsigned_literal_expr(value: u64) -> PureExpr {
    if let Ok(value) = i64::try_from(value) {
        return PureExpr::Int(value);
    }
    let [a, b, c, d, e, f, g, h] = value.to_le_bytes();
    let high = PureExpr::Int(i64::from(u32::from_le_bytes([e, f, g, h])));
    let low = PureExpr::Int(i64::from(u32::from_le_bytes([a, b, c, d])));
    PureExpr::BinOp(
        Arc::new(PureExpr::BinOp(
            Arc::new(high),
            BinOp::Mul,
            Arc::new(PureExpr::Int(1_i64 << 32)),
        )),
        BinOp::Add,
        Arc::new(low),
    )
}
