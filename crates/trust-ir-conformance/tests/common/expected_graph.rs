// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Encode finite handwritten expectations, never interpreter/oracle output.

use super::{Val, compact_value_graph::Graph};
use serde_json::{Value as Json, json};

pub(super) fn expected_graph(values: &[Val]) -> Result<Graph, String> {
    fn add(nodes: &mut Vec<Json>, node: Json) -> usize {
        let id = nodes.len();
        nodes.push(node);
        id
    }
    fn list(nodes: &mut Vec<Json>, values: &[Val]) -> Result<usize, String> {
        let ids = values
            .iter()
            .map(|v| value(nodes, v))
            .collect::<Result<Vec<_>, _>>()?;
        let mut tail = add(nodes, json!(["nil"]));
        for id in ids.into_iter().rev() {
            tail = add(nodes, json!(["cons", id, tail]));
        }
        Ok(tail)
    }
    fn value(nodes: &mut Vec<Json>, v: &Val) -> Result<usize, String> {
        let node = match v {
            Val::Int { width, raw } => json!(["int", width, raw.to_string()]),
            Val::Bool(b) => json!(["bool", b]),
            Val::Float(bits) => json!(["float", bits.to_string()]),
            Val::Nan => json!(["float", "nan"]),
            Val::Ptr { null: is_null } => json!(["ptr", is_null]),
            Val::FatPtr(a, b) => {
                let a = value(nodes, a)?;
                let b = value(nodes, b)?;
                json!(["fatptr", a, b])
            }
            Val::Unit => json!(["aggregate", list(nodes, &[])?]),
            Val::Aggregate(vs) | Val::Vector(vs) | Val::Sequence(vs) | Val::Set(vs) => {
                let tag = match v {
                    Val::Aggregate(_) => "aggregate",
                    Val::Vector(_) => "vector",
                    Val::Sequence(_) => "sequence",
                    _ => "set",
                };
                json!([tag, list(nodes, vs)?])
            }
            Val::Array(vs) => {
                let list = list(nodes, vs)?;
                let tree = add(nodes, json!(["dense", list]));
                json!(["array", vs.len().to_string(), tree])
            }
            Val::Record(fields) => {
                let ids = fields
                    .iter()
                    .map(|(_, v)| value(nodes, v))
                    .collect::<Result<Vec<_>, _>>()?;
                let mut tail = add(nodes, json!(["nil"]));
                for ((name, _), id) in fields.iter().zip(ids).rev() {
                    tail = add(nodes, json!(["field", name, id, tail]));
                }
                json!(["record", tail])
            }
            Val::Closure { func, captures } => json!(["closure", func, list(nodes, captures)?]),
            Val::Function { signature, func } => json!(["function", signature, func]),
            Val::FnItem(func) => json!(["fnitem", func]),
            Val::Uninit => json!(["uninit"]),
            Val::PtrAt { .. } | Val::Tensor { .. } | Val::Other(_) => {
                return Err("expectation has no W5b graph observation".into());
            }
        };
        Ok(add(nodes, node))
    }
    let mut nodes = Vec::new();
    let roots = values
        .iter()
        .map(|v| value(&mut nodes, v))
        .collect::<Result<Vec<_>, _>>()?;
    Graph::decode(&json!({"graph":{"version":2,"nodes":nodes,"roots":roots}}))
}
