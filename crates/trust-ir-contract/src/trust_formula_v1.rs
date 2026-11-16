//! The shared TrustFormulaV1 wire grammar and expression fold.
//!
//! This module reads one schema; it does not introduce an expression IR or a
//! proof checker. The algebra constructs the consumer's existing expressions.
//! Parsing-stack budgets, original payload identity and replay definedness stay
//! with their callers. The two named policies retain the existing ingress
//! boundaries: strict machine-contract predicates and legacy native replay.

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use serde_json::{Map, Value};

/// Canonical producer spelling. Compatibility never rewrites original bytes.
pub const TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION: &str = "trust_wp.trust-formula.v1";
/// Historical replay spelling, also used when comparing separator aliases.
pub const TRUST_FORMULA_CLAIM_SCHEMA_VERSION: &str = "trust-wp.trust-formula.v1";

/// Fixed consumer fragments of the same wire grammar, not proof authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodePolicy {
    /// Exact canonical schema, no arithmetic, well-sorted Boolean predicate.
    CanonicalArithmeticFree,
    /// Existing native arithmetic grammar and legacy typing boundary.
    ///
    /// In particular, general operand/root typing remains the native request
    /// checker's responsibility. Declared let-value sorts and modeled
    /// quantifier domains are still checked here, as in the original reader.
    NativeReplay,
}

/// Sort vocabulary of this wire format, separate from SMT `Sort`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WireSort {
    Bool,
    Int,
    Seq,
    Ref { mutable: bool, inner: Box<Self> },
    TypeParam(char),
}

impl fmt::Display for WireSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => f.write_str("Bool"),
            Self::Int => f.write_str("Int"),
            Self::Seq => f.write_str("Seq"),
            Self::Ref {
                mutable: false,
                inner,
            } => write!(f, "&{inner}"),
            Self::Ref {
                mutable: true,
                inner,
            } => write!(f, "&mut {inner}"),
            Self::TypeParam(name) => write!(f, "TypeParam({name})"),
        }
    }
}

/// Exact JSON integer, with the old signed-first interpretation preserved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegerLiteral {
    I64(i64),
    U64(u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
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
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quantifier {
    Forall,
    Exists,
}

/// Construct the consumer's expression representation after reading the
/// shared grammar. Constructors receive resolved names and sorts; they never
/// decode JSON fields or choose a schema, scope or arithmetic policy.
pub trait Algebra {
    type Expr;
    fn bool_literal(&mut self, value: bool) -> Self::Expr;
    fn integer_literal(&mut self, value: IntegerLiteral) -> Self::Expr;
    fn variable(&mut self, name: &str, sort: &WireSort) -> Self::Expr;
    fn old(&mut self, inner: Self::Expr) -> Self::Expr;
    fn unary(&mut self, op: UnaryOp, inner: Self::Expr) -> Self::Expr;
    fn binary(&mut self, op: BinaryOp, lhs: Self::Expr, rhs: Self::Expr) -> Self::Expr;
    fn let_binding(
        &mut self,
        name: &str,
        sort: &WireSort,
        value: Self::Expr,
        body: Self::Expr,
    ) -> Self::Expr;
    fn quantified(
        &mut self,
        kind: Quantifier,
        name: &str,
        sort: &WireSort,
        body: Self::Expr,
    ) -> Self::Expr;
}

/// Decoded ordinary data. This record carries no proof grade or source claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodedClaim<E> {
    /// Original variable order, followed by the optional result declaration.
    pub declarations: Vec<(String, WireSort)>,
    pub result_name: Option<String>,
    pub body: E,
    /// Syntax-derived sort. `NativeReplay` deliberately retains its original
    /// later typing boundary; this field alone asserts no well-sortedness.
    pub body_sort: WireSort,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodeError {
    message: String,
}

impl DecodeError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}
impl Error for DecodeError {}

/// Built-in algebra for callers that only validate and retain the original
/// JSON for canonical serialization. There is no duplicate validation walker.
#[derive(Clone, Copy, Debug, Default)]
pub struct ValidationAlgebra;
impl Algebra for ValidationAlgebra {
    type Expr = ();
    fn bool_literal(&mut self, _: bool) {}
    fn integer_literal(&mut self, _: IntegerLiteral) {}
    fn variable(&mut self, _: &str, _: &WireSort) {}
    fn old(&mut self, _: ()) {}
    fn unary(&mut self, _: UnaryOp, _: ()) {}
    fn binary(&mut self, _: BinaryOp, _: (), _: ()) {}
    fn let_binding(&mut self, _: &str, _: &WireSort, _: (), _: ()) {}
    fn quantified(&mut self, _: Quantifier, _: &str, _: &WireSort, _: ()) {}
}

pub fn validate_value(
    value: &Value,
    policy: DecodePolicy,
) -> Result<DecodedClaim<()>, DecodeError> {
    decode_value(value, policy, &mut ValidationAlgebra)
}

/// Decode an already-parsed value without modifying it. Raw-text callers use
/// the common `proof_json::UniqueJsonValue` through their bounded entrypoint.
pub fn decode_value<A: Algebra>(
    value: &Value,
    policy: DecodePolicy,
    algebra: &mut A,
) -> Result<DecodedClaim<A::Expr>, DecodeError> {
    let object = value.as_object().ok_or_else(|| {
        DecodeError::new(match policy {
            DecodePolicy::NativeReplay => "claim payload must be a JSON object".to_owned(),
            DecodePolicy::CanonicalArithmeticFree => format!(
                "typed `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}` predicate must be a JSON object"
            ),
        })
    })?;
    reject_unknown_fields(object, "claim", &["schema", "variables", "result", "body"])?;
    let schema = required_str(object.get("schema"), "schema")?;
    let schema_ok = match policy {
        DecodePolicy::CanonicalArithmeticFree => schema == TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION,
        DecodePolicy::NativeReplay => {
            schema.replace('_', "-") == TRUST_FORMULA_CLAIM_SCHEMA_VERSION
        }
    };
    if !schema_ok {
        return Err(DecodeError::new(match policy {
            DecodePolicy::NativeReplay => format!(
                "unsupported trust formula schema `{schema}`; expected `{TRUST_FORMULA_CLAIM_SCHEMA_VERSION}`"
            ),
            DecodePolicy::CanonicalArithmeticFree => format!(
                "typed TrustFormulaV1 predicate uses schema `{schema}`, expected `{TRUST_WP_TRUST_FORMULA_SCHEMA_VERSION}`"
            ),
        }));
    }
    let mut env = BTreeMap::new();
    let mut declarations = Vec::new();
    if let Some(variables) = object.get("variables") {
        let variables = variables
            .as_array()
            .ok_or_else(|| DecodeError::new("variables must be an array"))?;
        for (index, value) in variables.iter().enumerate() {
            let (name, sort) = binding(value, &format!("variables[{index}]"), false, policy)?;
            insert_binding(&mut env, name, sort.clone(), policy)?;
            declarations.push((name.to_owned(), sort));
        }
    }
    let result_name = if let Some(value) = object.get("result") {
        let (name, sort) = binding(value, "result", true, policy)?;
        insert_binding(&mut env, name, sort.clone(), policy)?;
        declarations.push((name.to_owned(), sort));
        Some(name)
    } else {
        None
    };
    let body = object
        .get("body")
        .ok_or_else(|| DecodeError::new("missing required field `body`"))?;
    let mut decoder = Decoder {
        policy,
        env,
        result_name,
        algebra,
    };
    let node = decoder.expression(body, &mut "body".to_owned())?;
    if policy == DecodePolicy::CanonicalArithmeticFree {
        require_sort(&node.sort, &WireSort::Bool, "body")?;
    }
    Ok(DecodedClaim {
        declarations,
        result_name: result_name.map(str::to_owned),
        body: node.expr,
        body_sort: node.sort,
    })
}

struct Node<E> {
    expr: E,
    sort: WireSort,
}
struct Decoder<'a, 'b, A: Algebra> {
    policy: DecodePolicy,
    env: BTreeMap<&'a str, WireSort>,
    result_name: Option<&'a str>,
    algebra: &'b mut A,
}

impl<'a, A: Algebra> Decoder<'a, '_, A> {
    fn child(
        &mut self,
        value: &'a Value,
        path: &mut String,
        suffix: &str,
    ) -> Result<Node<A::Expr>, DecodeError> {
        let len = path.len();
        path.push_str(suffix);
        let answer = self.expression(value, path);
        path.truncate(len);
        answer
    }

    fn expression(
        &mut self,
        value: &'a Value,
        path: &mut String,
    ) -> Result<Node<A::Expr>, DecodeError> {
        let object = value
            .as_object()
            .ok_or_else(|| DecodeError::new(format!("{path} must be an object")))?;
        if let Some(value) = object.get("bool") {
            reject_unknown_fields(object, path, &["bool"])?;
            let value = value
                .as_bool()
                .ok_or_else(|| DecodeError::new(format!("{path}.bool must be a boolean")))?;
            return Ok(Node {
                expr: self.algebra.bool_literal(value),
                sort: WireSort::Bool,
            });
        }
        if let Some(value) = object.get("int") {
            reject_unknown_fields(object, path, &["int"])?;
            let value = value
                .as_i64()
                .map(IntegerLiteral::I64)
                .or_else(|| value.as_u64().map(IntegerLiteral::U64))
                .ok_or_else(|| {
                    DecodeError::new(format!(
                        "{path}.int must be an exact signed or unsigned 64-bit integer"
                    ))
                })?;
            return Ok(Node {
                expr: self.algebra.integer_literal(value),
                sort: WireSort::Int,
            });
        }
        if let Some(value) = object.get("var") {
            reject_unknown_fields(object, path, &["var"])?;
            let name = value
                .as_str()
                .ok_or_else(|| DecodeError::new(format!("{path}.var must be a string")))?;
            let sort = self.env.get(name).cloned().ok_or_else(|| {
                DecodeError::new(format!("{path}.var references undeclared binding `{name}`"))
            })?;
            return Ok(Node {
                expr: self.algebra.variable(name, &sort),
                sort,
            });
        }
        if let Some(value) = object.get("result") {
            reject_unknown_fields(object, path, &["result"])?;
            if value.as_bool() != Some(true) {
                return Err(DecodeError::new(format!(
                    "{path}.result must be boolean true"
                )));
            }
            let name = self.result_name.ok_or_else(|| {
                DecodeError::new(format!("{path}.result requires a top-level result binding"))
            })?;
            let sort = self.env.get(name).cloned().ok_or_else(|| {
                DecodeError::new("top-level result binding is missing from environment")
            })?;
            return Ok(Node {
                expr: self.algebra.variable(name, &sort),
                sort,
            });
        }
        if let Some(value) = object.get("old") {
            reject_unknown_fields(object, path, &["old"])?;
            let inner = self.child(value, path, ".old")?;
            return Ok(Node {
                expr: self.algebra.old(inner.expr),
                sort: inner.sort,
            });
        }
        let op = required_str(object.get("op"), &format!("{path}.op"))?;
        if self.policy == DecodePolicy::CanonicalArithmeticFree {
            if let Some(label) = arithmetic_op_label(op) {
                return Err(DecodeError::new(arithmetic_refusal(label)));
            }
        }
        match op {
            "not" | "neg" => {
                reject_unknown_fields(object, path, &["op", "expr"])?;
                let inner = required_value(object, "expr", path)?;
                let inner = self.child(inner, path, ".expr")?;
                let (op, sort) = if op == "not" {
                    (UnaryOp::Not, WireSort::Bool)
                } else {
                    (UnaryOp::Neg, WireSort::Int)
                };
                if self.policy == DecodePolicy::CanonicalArithmeticFree {
                    require_sort(&inner.sort, &sort, &format!("{path}.expr"))?;
                }
                Ok(Node {
                    expr: self.algebra.unary(op, inner.expr),
                    sort,
                })
            }
            "let" => self.let_expression(object, path),
            "forall" | "exists" => self.quantifier_expression(op, object, path),
            "add" | "sub" | "mul" | "div" | "mod" | "eq" | "ne" | "lt" | "le" | "gt" | "ge"
            | "and" | "or" | "implies" => self.binary_expression(op, object, path),
            unsupported => Err(DecodeError::new(match self.policy {
                DecodePolicy::NativeReplay => format!(
                    "{path}.op `{unsupported}` is outside the trust-formula v1 native int/bool fragment"
                ),
                DecodePolicy::CanonicalArithmeticFree => format!(
                    "{path}.op `{unsupported}` is outside the arithmetic-free TrustFormulaV1 fragment"
                ),
            })),
        }
    }

    fn let_expression(
        &mut self,
        object: &'a Map<String, Value>,
        path: &mut String,
    ) -> Result<Node<A::Expr>, DecodeError> {
        reject_unknown_fields(object, path, &["op", "name", "sort", "value", "body"])?;
        let (name, sort) = named_sort(object, path, self.policy)?;
        if self.env.contains_key(name) {
            return Err(DecodeError::new(format!(
                "{path}.name shadows existing binding `{name}`"
            )));
        }
        let value = required_value(object, "value", path)?;
        let body = required_value(object, "body", path)?;
        let value = self.child(value, path, ".value")?;
        if value.sort != sort {
            return Err(DecodeError::new(match self.policy {
                DecodePolicy::NativeReplay => format!(
                    "{path} declares `{name}` at sort `{sort}` but binds it to a value of sort `{}`",
                    value.sort
                ),
                DecodePolicy::CanonicalArithmeticFree => format!(
                    "{path}.value has sort {:?}, expected {sort:?} in TrustFormulaV1",
                    value.sort
                ),
            }));
        }
        self.env.insert(name, sort.clone());
        let body = self.child(body, path, ".body");
        self.env.remove(name);
        let body = body?;
        Ok(Node {
            expr: self.algebra.let_binding(name, &sort, value.expr, body.expr),
            sort: body.sort,
        })
    }

    fn quantifier_expression(
        &mut self,
        op: &str,
        object: &'a Map<String, Value>,
        path: &mut String,
    ) -> Result<Node<A::Expr>, DecodeError> {
        reject_unknown_fields(object, path, &["op", "name", "sort", "body"])?;
        let (name, sort) = named_sort(object, path, self.policy)?;
        if self.env.contains_key(name) {
            return Err(DecodeError::new(format!(
                "{path}.name shadows existing binding `{name}`"
            )));
        }
        if self.policy == DecodePolicy::NativeReplay
            && !matches!(sort, WireSort::Int | WireSort::Bool | WireSort::Ref { .. })
        {
            let written = required_str(object.get("sort"), &format!("{path}.sort"))?;
            return Err(DecodeError::new(format!(
                "{path}.sort `{written}` is a quantifier sort native replay does not model: a binder ranges over `int`, `bool` or a reference"
            )));
        }
        let body = required_value(object, "body", path)?;
        self.env.insert(name, sort.clone());
        let body = self.child(body, path, ".body");
        self.env.remove(name);
        let body = body?;
        if self.policy == DecodePolicy::CanonicalArithmeticFree {
            require_sort(&body.sort, &WireSort::Bool, &format!("{path}.body"))?;
        }
        let quantifier = if op == "forall" {
            Quantifier::Forall
        } else {
            Quantifier::Exists
        };
        Ok(Node {
            expr: self.algebra.quantified(quantifier, name, &sort, body.expr),
            sort: WireSort::Bool,
        })
    }

    fn binary_expression(
        &mut self,
        label: &str,
        object: &'a Map<String, Value>,
        path: &mut String,
    ) -> Result<Node<A::Expr>, DecodeError> {
        reject_unknown_fields(object, path, &["op", "lhs", "rhs"])?;
        let lhs_value = required_value(object, "lhs", path)?;
        let rhs_value = required_value(object, "rhs", path)?;
        let lhs = self.child(lhs_value, path, ".lhs")?;
        let rhs = self.child(rhs_value, path, ".rhs")?;
        let op = match label {
            "add" => BinaryOp::Add,
            "sub" => BinaryOp::Sub,
            "mul" => BinaryOp::Mul,
            "div" => BinaryOp::Div,
            "mod" => BinaryOp::Mod,
            "eq" => BinaryOp::Eq,
            "ne" => BinaryOp::Ne,
            "lt" => BinaryOp::Lt,
            "le" => BinaryOp::Le,
            "gt" => BinaryOp::Gt,
            "ge" => BinaryOp::Ge,
            "and" => BinaryOp::And,
            "or" => BinaryOp::Or,
            "implies" => BinaryOp::Implies,
            _ => return Err(DecodeError::new("unsupported binary operator")),
        };
        if self.policy == DecodePolicy::CanonicalArithmeticFree {
            match op {
                BinaryOp::Eq | BinaryOp::Ne => {
                    require_sort(&rhs.sort, &lhs.sort, &format!("{path}.rhs"))?;
                    if lhs.sort == WireSort::Seq && lhs_value != rhs_value {
                        return Err(DecodeError::new(format!(
                            "{path} compares distinct Seq expressions; native TrustFormulaV1 replay supports only structurally reflexive Seq equality"
                        )));
                    }
                }
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                    require_sort(&lhs.sort, &WireSort::Int, &format!("{path}.lhs"))?;
                    require_sort(&rhs.sort, &WireSort::Int, &format!("{path}.rhs"))?;
                }
                BinaryOp::And | BinaryOp::Or | BinaryOp::Implies => {
                    require_sort(&lhs.sort, &WireSort::Bool, &format!("{path}.lhs"))?;
                    require_sort(&rhs.sort, &WireSort::Bool, &format!("{path}.rhs"))?;
                }
                _ => return Err(DecodeError::new(arithmetic_refusal(label))),
            }
        }
        let sort = match op {
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                WireSort::Int
            }
            _ => WireSort::Bool,
        };
        Ok(Node {
            expr: self.algebra.binary(op, lhs.expr, rhs.expr),
            sort,
        })
    }
}

fn binding<'a>(
    value: &'a Value,
    path: &str,
    result: bool,
    policy: DecodePolicy,
) -> Result<(&'a str, WireSort), DecodeError> {
    let object = value
        .as_object()
        .ok_or_else(|| DecodeError::new(format!("{path} must be an object")))?;
    reject_unknown_fields(object, path, &["name", "sort"])?;
    let name = if result && !object.contains_key("name") {
        "result"
    } else {
        required_str(object.get("name"), &format!("{path}.name"))?
    };
    validate_name(name, &format!("{path}.name"))?;
    let sort = required_str(object.get("sort"), &format!("{path}.sort"))?;
    Ok((name, decode_sort(sort, path, policy)?))
}

fn named_sort<'a>(
    object: &'a Map<String, Value>,
    path: &str,
    policy: DecodePolicy,
) -> Result<(&'a str, WireSort), DecodeError> {
    let name = required_str(object.get("name"), &format!("{path}.name"))?;
    validate_name(name, &format!("{path}.name"))?;
    let sort = required_str(object.get("sort"), &format!("{path}.sort"))?;
    Ok((name, decode_sort(sort, path, policy)?))
}

fn insert_binding<'a>(
    env: &mut BTreeMap<&'a str, WireSort>,
    name: &'a str,
    sort: WireSort,
    policy: DecodePolicy,
) -> Result<(), DecodeError> {
    if env.insert(name, sort).is_some() {
        return Err(DecodeError::new(match policy {
            DecodePolicy::NativeReplay => format!("duplicate binding `{name}`"),
            DecodePolicy::CanonicalArithmeticFree => {
                format!("duplicate TrustFormulaV1 binding `{name}`")
            }
        }));
    }
    Ok(())
}

fn decode_sort(written: &str, path: &str, policy: DecodePolicy) -> Result<WireSort, DecodeError> {
    let sort = written.trim();
    if let Some(inner) = sort.strip_prefix("&mut ") {
        return Ok(WireSort::Ref {
            mutable: true,
            inner: Box::new(decode_sort(inner, path, policy)?),
        });
    }
    if let Some(inner) = sort.strip_prefix('&') {
        return Ok(WireSort::Ref {
            mutable: false,
            inner: Box::new(decode_sort(inner, path, policy)?),
        });
    }
    if sort.starts_with('[') && sort.ends_with(']') {
        let inner = sort[1..sort.len() - 1].trim();
        if inner.is_empty() {
            return Err(DecodeError::new(format!(
                "{path}.sort slice element type is empty"
            )));
        }
        decode_sort(inner, path, policy)?;
        return Ok(WireSort::Seq);
    }
    match sort {
        "int" | "Int" => Ok(WireSort::Int),
        "bool" | "Bool" => Ok(WireSort::Bool),
        "seq" | "Seq" => Ok(WireSort::Seq),
        _ => {
            let mut chars = sort.chars();
            if let (Some(ch), None) = (chars.next(), chars.next()) {
                if ch.is_ascii_uppercase() {
                    return Ok(WireSort::TypeParam(ch));
                }
            }
            Err(DecodeError::new(match policy {
                DecodePolicy::NativeReplay => format!(
                    "{path}.sort `{sort}` is outside the trust-formula v1 native replay sort fragment"
                ),
                DecodePolicy::CanonicalArithmeticFree => {
                    format!("{path}.sort `{sort}` is outside the TrustFormulaV1 sort fragment")
                }
            }))
        }
    }
}

fn require_sort(actual: &WireSort, expected: &WireSort, path: &str) -> Result<(), DecodeError> {
    if actual == expected {
        Ok(())
    } else {
        Err(DecodeError::new(format!(
            "{path} has sort {actual:?}, expected {expected:?} in TrustFormulaV1"
        )))
    }
}

fn required_str<'a>(value: Option<&'a Value>, path: &str) -> Result<&'a str, DecodeError> {
    value
        .ok_or_else(|| DecodeError::new(format!("missing required field `{path}`")))?
        .as_str()
        .ok_or_else(|| DecodeError::new(format!("{path} must be a string")))
}

fn required_value<'a>(
    object: &'a Map<String, Value>,
    name: &str,
    path: &str,
) -> Result<&'a Value, DecodeError> {
    object
        .get(name)
        .ok_or_else(|| DecodeError::new(format!("{path}.{name} is required")))
}

fn validate_name(name: &str, path: &str) -> Result<(), DecodeError> {
    let mut chars = name.chars();
    let first = chars
        .next()
        .ok_or_else(|| DecodeError::new(format!("{path} is empty")))?;
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return Err(DecodeError::new(format!(
            "{path} must start with `_` or an ASCII letter"
        )));
    }
    if !chars.all(|ch| {
        ch == '_'
            || ch.is_ascii_alphanumeric()
            || matches!(ch, '#' | '.' | '[' | ']' | '*' | '@' | '-' | ';' | '=')
    }) {
        return Err(DecodeError::new(format!(
            "{path} contains characters outside the supported SMT-symbol set"
        )));
    }
    Ok(())
}

fn reject_unknown_fields(
    object: &Map<String, Value>,
    path: &str,
    allowed: &[&str],
) -> Result<(), DecodeError> {
    if let Some(field) = object
        .keys()
        .find(|field| !allowed.contains(&field.as_str()))
    {
        return Err(DecodeError::new(format!(
            "{path} contains unsupported field `{field}`"
        )));
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

fn arithmetic_refusal(op: &str) -> String {
    format!(
        "Formula arithmetic operator `{op}` is outside the trust_wp.trust-formula.v1 arithmetic-free fragment: machine arithmetic modeled over unbounded Int is a false-proof vector (`result + 1 > result` is Int-provable but false at u64::MAX); see 2026-07-17 trust-wp lowering blueprint amendment 1"
    )
}
