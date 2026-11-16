// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validating reader for the compact observation protocol, not proof authority.
//! Validation and indexing visit stored nodes; logical array extents are never
//! materialized. Representation-independent whole-result comparison is separate.

use serde_json::Value as Json;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Value,
    List,
    Fields,
    Nil,
    Tree,
    Sequence,
}

#[derive(Clone, Copy, Debug)]
struct Measure {
    kind: Kind,
    len: u64,
}

#[derive(Debug, Clone)]
pub(super) struct Graph {
    nodes: Vec<Json>,
    measures: Vec<Measure>,
    roots: Vec<usize>,
}

type Result<T> = std::result::Result<T, String>;

fn number(j: &Json) -> Result<u64> {
    j.as_u64().ok_or_else(|| "expected unsigned integer".into())
}

fn decimal(j: &Json) -> Result<u64> {
    decimal_text(j)?
        .parse()
        .map_err(|_| "decimal exceeds u64 observation domain".into())
}

fn decimal_text(j: &Json) -> Result<&str> {
    let s = j.as_str().ok_or("expected decimal string")?;
    if s.is_empty() || !s.bytes().all(|c| c.is_ascii_digit()) || (s.len() > 1 && s.starts_with('0'))
    {
        return Err("expected canonical unsigned decimal".into());
    }
    Ok(s)
}

fn edge(measures: &[Measure], j: &Json, kind: Kind) -> Result<usize> {
    let i = usize::try_from(number(j)?).map_err(|_| "reference exceeds host index domain")?;
    let m = measures.get(i).ok_or("reference is not backward")?;
    let compatible = m.kind == kind
        || (m.kind == Kind::Nil && matches!(kind, Kind::List | Kind::Fields))
        || (kind == Kind::Sequence && matches!(m.kind, Kind::List | Kind::Tree | Kind::Nil));
    if !compatible {
        return Err("reference kind mismatch".into());
    }
    Ok(i)
}

fn arity(node: &[Json], n: usize) -> Result<()> {
    if node.len() == n {
        Ok(())
    } else {
        Err("node arity mismatch".into())
    }
}

impl Graph {
    pub(super) fn nodes(&self) -> &[Json] {
        &self.nodes
    }
    pub(super) fn roots(&self) -> &[usize] {
        &self.roots
    }

    pub(super) fn decode(j: &Json) -> Result<Self> {
        let outer = j.as_object().ok_or("expected graph object")?;
        if outer.len() != 1 {
            return Err("unexpected observation wrapper fields".into());
        }
        let graph = outer
            .get("graph")
            .and_then(Json::as_object)
            .ok_or("missing graph")?;
        if graph.len() != 3 || graph.get("version").and_then(Json::as_u64) != Some(2) {
            return Err("unsupported graph header".into());
        }
        let nodes = graph
            .get("nodes")
            .and_then(Json::as_array)
            .ok_or("missing nodes")?;
        let roots = graph
            .get("roots")
            .and_then(Json::as_array)
            .ok_or("missing roots")?;
        let mut measures: Vec<Measure> = Vec::with_capacity(nodes.len());
        for (index, wire) in nodes.iter().enumerate() {
            let check = || -> Result<Measure> {
                let n = wire.as_array().ok_or("expected node array")?;
                let tag = n.first().and_then(Json::as_str).ok_or("missing node tag")?;
                let mut measure = Measure {
                    kind: Kind::Value,
                    len: 0,
                };
                match tag {
                    "int" => {
                        arity(n, 3)?;
                        let width = number(&n[1])?;
                        let raw = decimal_text(&n[2])?
                            .parse::<u128>()
                            .map_err(|_| "integer exceeds u128")?;
                        if width > 128 || (width < 128 && raw >= (1u128 << width)) {
                            return Err("integer is not a width-normalized residue".into());
                        }
                    }
                    "float" => {
                        arity(n, 2)?;
                        if n[1].as_str() != Some("nan") {
                            let bits = decimal(&n[1])?;
                            if f64::from_bits(bits).is_nan() {
                                return Err("NaN must use canonical nan observation".into());
                            }
                        }
                    }
                    "bool" | "ptr" => {
                        arity(n, 2)?;
                        n[1].as_bool().ok_or("expected boolean")?;
                    }
                    "fatptr" => {
                        arity(n, 3)?;
                        let data = edge(&measures, &n[1], Kind::Value)?;
                        if nodes[data][0].as_str() != Some("ptr") {
                            return Err("fat pointer data is not a pointer observation".into());
                        }
                        edge(&measures, &n[2], Kind::Value)?;
                    }
                    "array" => {
                        arity(n, 3)?;
                        let len = decimal(&n[1])?;
                        let tree = edge(&measures, &n[2], Kind::Tree)?;
                        if len != measures[tree].len {
                            return Err("array extent mismatch".into());
                        }
                        measure.len = len;
                    }
                    "aggregate" => {
                        arity(n, 2)?;
                        let list = edge(&measures, &n[1], Kind::List)?;
                        measure.len = measures[list].len;
                    }
                    "vector" | "sequence" | "set" => {
                        arity(n, 2)?;
                        let content = edge(&measures, &n[1], Kind::Sequence)?;
                        measure.len = measures[content].len;
                    }
                    "record" => {
                        arity(n, 2)?;
                        edge(&measures, &n[1], Kind::Fields)?;
                    }
                    "closure" => {
                        arity(n, 3)?;
                        u32::try_from(number(&n[1])?).map_err(|_| "function id exceeds u32")?;
                        edge(&measures, &n[2], Kind::List)?;
                    }
                    "fnitem" => {
                        arity(n, 2)?;
                        u32::try_from(number(&n[1])?)
                            .map_err(|_| "function item id exceeds u32")?;
                    }
                    "function" => {
                        arity(n, 3)?;
                        for id in &n[1..] {
                            u32::try_from(number(id)?)
                                .map_err(|_| "function or signature id exceeds u32")?;
                        }
                    }
                    "frame" => {
                        arity(n, 2)?;
                        number(&n[1])?;
                    }
                    "poison" | "uninit" => arity(n, 1)?,
                    "nil" => {
                        arity(n, 1)?;
                        measure.kind = Kind::Nil;
                    }
                    "cons" | "field" => {
                        let is_field = tag == "field";
                        arity(n, if is_field { 4 } else { 3 })?;
                        let start = if is_field {
                            n[1].as_str().ok_or("expected field name")?;
                            2
                        } else {
                            1
                        };
                        edge(&measures, &n[start], Kind::Value)?;
                        let kind = if is_field { Kind::Fields } else { Kind::List };
                        let tail = edge(&measures, &n[start + 1], kind)?;
                        measure.kind = kind;
                        measure.len = measures[tail]
                            .len
                            .checked_add(1)
                            .ok_or("list extent overflow")?;
                    }
                    "empty" => {
                        arity(n, 1)?;
                        measure.kind = Kind::Tree;
                    }
                    "uniform" => {
                        arity(n, 3)?;
                        measure.kind = Kind::Tree;
                        measure.len = decimal(&n[1])?;
                        edge(&measures, &n[2], Kind::Value)?;
                    }
                    "dense" => {
                        arity(n, 2)?;
                        let list = edge(&measures, &n[1], Kind::List)?;
                        measure = Measure {
                            kind: Kind::Tree,
                            len: measures[list].len,
                        };
                    }
                    "concat" => {
                        arity(n, 3)?;
                        let left = edge(&measures, &n[1], Kind::Tree)?;
                        let right = edge(&measures, &n[2], Kind::Tree)?;
                        measure = Measure {
                            kind: Kind::Tree,
                            len: measures[left]
                                .len
                                .checked_add(measures[right].len)
                                .ok_or("tree extent overflow")?,
                        };
                    }
                    // Both runtimes retain repeated finite value templates with this tag.
                    "repeat" => {
                        arity(n, 3)?;
                        let unit = edge(&measures, &n[1], Kind::Tree)?;
                        measure = Measure {
                            kind: Kind::Tree,
                            len: measures[unit]
                                .len
                                .checked_mul(decimal(&n[2])?)
                                .ok_or("tree extent overflow")?,
                        };
                    }
                    _ => return Err(format!("unknown node tag {tag:?}")),
                }
                Ok(measure)
            };
            measures.push(check().map_err(|e| format!("node {index}: {e}"))?);
        }
        let roots = roots
            .iter()
            .map(|r| edge(&measures, r, Kind::Value))
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            nodes: nodes.clone(),
            measures,
            roots,
        })
    }

    /// Return a stored value node, not an expanded value. Every edge decreases
    /// its index; even an adversarial valid graph cannot cycle this traversal.
    pub(super) fn sequence_element(&self, value: usize, mut index: u64) -> Option<&Json> {
        let value_node = self.nodes.get(value)?.as_array()?;
        let child = match value_node[0].as_str()? {
            "array" => 2,
            "aggregate" | "vector" | "sequence" | "set" => 1,
            _ => return None,
        };
        if index >= self.measures[value].len {
            return None;
        }
        let mut content = value_node[child].as_u64()? as usize;
        loop {
            let n = self.nodes[content].as_array()?;
            match n[0].as_str()? {
                "uniform" => return self.nodes.get(n[2].as_u64()? as usize),
                "cons" => {
                    if index == 0 {
                        return self.nodes.get(n[1].as_u64()? as usize);
                    }
                    index -= 1;
                    content = n[2].as_u64()? as usize;
                }
                "dense" => content = n[1].as_u64()? as usize,
                "concat" => {
                    let left = n[1].as_u64()? as usize;
                    if index < self.measures[left].len {
                        content = left;
                    } else {
                        index -= self.measures[left].len;
                        content = n[2].as_u64()? as usize;
                    }
                }
                "repeat" => {
                    content = n[1].as_u64()? as usize;
                    index %= self.measures[content].len;
                }
                _ => return None,
            }
        }
    }
}

#[test]
fn compact_graph_huge_extents_and_periodic_queries_stay_structural() {
    use serde_json::json;
    let j = json!({"graph":{"version":2,"nodes":[
        ["int",32,"7"],["uniform",u64::MAX.to_string(),0],["array",u64::MAX.to_string(),1],
        ["int",32,"42"],["uniform",(u64::MAX-1).to_string(),0],["uniform","1",3],
        ["concat",4,5],["array",u64::MAX.to_string(),6],
        ["nil"],["cons",3,8],["cons",0,9],["dense",10],["repeat",11,"3"],["array","6",12],
        ["uniform","1",2],["repeat",14,u64::MAX.to_string()],["array",u64::MAX.to_string(),15]
    ],"roots":[2,7,13,16,2]}});
    let g = Graph::decode(&j).unwrap();
    assert_eq!(g.nodes.len(), 17);
    assert_eq!(g.roots, [2, 7, 13, 16, 2]);
    for index in [0, 1, u64::MAX - 1] {
        assert_eq!(g.sequence_element(2, index), Some(&g.nodes[0]));
    }
    assert_eq!(g.sequence_element(2, u64::MAX), None);
    assert_eq!(g.sequence_element(7, u64::MAX - 2), Some(&g.nodes[0]));
    assert_eq!(g.sequence_element(7, u64::MAX - 1), Some(&g.nodes[3]));
    assert_eq!(g.sequence_element(7, u64::MAX), None);
    for index in 0..6 {
        assert_eq!(
            g.sequence_element(13, index),
            Some(&g.nodes[if index % 2 == 0 { 0 } else { 3 }])
        );
    }
    assert_eq!(g.sequence_element(13, 6), None);
    assert_eq!(g.sequence_element(16, u64::MAX - 1), Some(&g.nodes[2]));
    assert_eq!(g.sequence_element(0, 0), None);
    assert_eq!(g.sequence_element(usize::MAX, 0), None);
    // A well-formed but wrong representation must expose the wrong value;
    // rejecting malformed inputs alone would not establish reader usefulness.
    let mut swapped = j.clone();
    swapped["graph"]["nodes"][6] = json!(["concat", 5, 4]);
    let wrong = Graph::decode(&swapped).unwrap();
    assert_ne!(wrong.sequence_element(7, 0), g.sequence_element(7, 0));
    assert_eq!(wrong.sequence_element(7, 0), Some(&g.nodes[3]));
}

#[test]
fn compact_graph_all_value_tags_and_empty_shapes_validate() {
    use serde_json::json;
    let j = json!({"graph":{"version":2,"nodes":[
        ["nil"],["int",128,u128::MAX.to_string()],["bool",true],["ptr",false],
        ["float","nan"],["float",(-0.0f64).to_bits().to_string()],["fatptr",3,1],
        ["cons",1,0],["field","λ",2,0],["aggregate",7],["vector",7],["sequence",7],["set",7],
        ["record",8],["closure",4294967295u32,7],["function",0,1],["frame",2],["poison"],["uninit"],
        ["empty"],["array","0",19],["dense",0],["array","0",21],["repeat",19,u64::MAX.to_string()],
        ["array","0",23],["int",0,"0"],["record",0],["aggregate",0]
    ],"roots":[1,2,3,4,5,6,9,10,11,12,13,14,15,16,17,18,20,22,24,25,26,27]}});
    let g = Graph::decode(&j).unwrap();
    assert_eq!(g.roots.len(), 22);
    for array in [20, 22, 24] {
        assert_eq!(g.sequence_element(array, 0), None);
    }
    assert!(
        Graph::decode(&json!({"graph":{"version":2,"nodes":[],"roots":[]}}))
            .unwrap()
            .roots
            .is_empty()
    );
}

#[test]
fn compact_graph_malformed_observations_refuse_by_cause() {
    use serde_json::json;
    let base = json!({"graph":{"version":2,"nodes":[["int",8,"7"],["uniform","2",0],["array","2",1]],"roots":[2]}});
    Graph::decode(&base).unwrap();
    let cases: Vec<(&str, Json, &str)> = vec![
        ("self edge", json!(["uniform", "2", 1]), "not backward"),
        ("future edge", json!(["uniform", "2", 2]), "not backward"),
        (
            "negative edge",
            json!(["uniform", "2", -1]),
            "unsigned integer",
        ),
        (
            "fractional edge",
            json!(["uniform", "2", 0.5]),
            "unsigned integer",
        ),
        ("wrong kind", json!(["dense", 0]), "kind mismatch"),
        ("extra field", json!(["uniform", "2", 0, 0]), "arity"),
        ("missing field", json!(["uniform", "2"]), "arity"),
        (
            "unknown tag",
            json!(["future-tree", "2", 0]),
            "unknown node",
        ),
        (
            "decimal leading zero",
            json!(["uniform", "02", 0]),
            "canonical",
        ),
        ("decimal negative", json!(["uniform", "-2", 0]), "canonical"),
        (
            "decimal overflow",
            json!(["uniform", "18446744073709551616", 0]),
            "u64",
        ),
        ("bad field", json!(["field", 1, 0, 0]), "field name"),
        ("bad float", json!(["float", "unencodable"]), "canonical"),
        (
            "NaN bits",
            json!(["float", f64::NAN.to_bits().to_string()]),
            "NaN",
        ),
        ("fat pointer data", json!(["fatptr", 0, 0]), "not a pointer"),
        (
            "signature overflow",
            json!(["function", 4294967296u64, 0]),
            "u32",
        ),
    ];
    for (label, node, cause) in cases {
        let mut j = base.clone();
        j["graph"]["nodes"][1] = node;
        let error = Graph::decode(&j).unwrap_err();
        assert!(error.contains(cause), "{label}: {error}");
    }
    for (label, path, value, cause) in [
        (
            "raw overflow",
            vec!["nodes", "0", "2"],
            json!("256"),
            "residue",
        ),
        (
            "width overflow",
            vec!["nodes", "0", "1"],
            json!(129),
            "residue",
        ),
        (
            "array extent",
            vec!["nodes", "2", "1"],
            json!("3"),
            "extent mismatch",
        ),
        ("tree root", vec!["roots", "0"], json!(1), "kind mismatch"),
        ("missing root", vec!["roots", "0"], json!(3), "not backward"),
        ("version", vec!["version"], json!(1), "header"),
    ] {
        let mut j = base.clone();
        let mut at = &mut j["graph"];
        for key in path {
            at = if let Ok(i) = key.parse::<usize>() {
                &mut at[i]
            } else {
                &mut at[key]
            };
        }
        *at = value;
        let error = Graph::decode(&j).unwrap_err();
        assert!(error.contains(cause), "{label}: {error}");
    }
    for (tag, last, cause) in [
        ("concat", json!(1), "overflow"),
        ("repeat", json!("2"), "overflow"),
    ] {
        let mut j = base.clone();
        j["graph"]["nodes"][1][1] = json!(u64::MAX.to_string());
        j["graph"]["nodes"][2] = json!([tag, 1, last]);
        assert!(Graph::decode(&j).unwrap_err().contains(cause));
    }
    for node in [
        json!(["aggregate", 1]),
        json!(["record", 1]),
        json!(["closure", 4, 1]),
    ] {
        let mut j = base.clone();
        j["graph"]["nodes"][2] = node;
        assert!(Graph::decode(&j).unwrap_err().contains("kind mismatch"));
    }
    let mut j = base.clone();
    j["graph"]["nodes"][1] = json!(["vector", 0]);
    assert!(Graph::decode(&j).unwrap_err().contains("kind mismatch"));
    let mut j = base;
    j["extra"] = json!(true);
    assert!(Graph::decode(&j).unwrap_err().contains("wrapper"));
}

pub(super) fn lean_corpus() -> Option<Vec<Json>> {
    if matches!(super::oracle(), super::Oracle::Absent) {
        return None;
    }
    let lake = super::find_lake().expect("built oracle has lake");
    let mut command = super::lake_run_command(
        &lake,
        &super::lean_dir(),
        "TrustIrEval/ObservationCorpus.lean",
    );
    let out = command
        .output()
        .expect("run actual Lean observation serializer");
    assert!(
        out.status.success(),
        "Lean corpus failed: {}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8(out.stdout).unwrap();
    let rows = text
        .lines()
        .map(|line| serde_json::from_str::<Json>(line).expect("one graph per line"))
        .collect::<Vec<_>>();
    Some(rows)
}

#[test]
fn compact_graph_reader_consumes_actual_lean_serializer_outputs() {
    let Some(rows) = lean_corpus() else {
        return;
    };
    assert_eq!(rows.len(), 8);
    let graphs = rows
        .iter()
        .map(|j| Graph::decode(j).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(graphs[0].nodes.len(), 3);
    assert_eq!(
        graphs[0].sequence_element(graphs[0].roots[0], u64::MAX - 1),
        Some(&serde_json::json!(["int", 32, "7"]))
    );
    for (i, raw) in [(0, "7"), (u64::MAX - 2, "7"), (u64::MAX - 1, "42")] {
        assert_eq!(
            graphs[1].sequence_element(graphs[1].roots[0], i),
            Some(&serde_json::json!(["int", 32, raw]))
        );
    }
    assert_eq!(
        graphs[1].sequence_element(graphs[1].roots[0], u64::MAX),
        None
    );
    assert_eq!(graphs[2].roots.len(), 19);
    // Typed and legacy closure spelling intentionally follows the existing
    // observation policy; this reader grants no missing nominal-type license.
    assert_eq!(graphs[2].roots[12], graphs[2].roots[13]);
    for i in 0..65 {
        assert_eq!(
            graphs[3].sequence_element(graphs[3].roots[0], i),
            Some(&serde_json::json!(["int", 32, i.to_string()]))
        );
    }
    assert_eq!(graphs[3].sequence_element(graphs[3].roots[0], 65), None);
    assert!(graphs[4].nodes.iter().any(|node| node[0] == "repeat"));
    for index in [0, 1, 2, 3, u64::MAX - 2, u64::MAX - 1] {
        let raw = [22, 33, 11][(index % 3) as usize];
        assert_eq!(
            graphs[4].sequence_element(graphs[4].roots[0], index),
            Some(&serde_json::json!(["int", 32, raw.to_string()]))
        );
    }
    assert_eq!(
        graphs[4].sequence_element(graphs[4].roots[0], u64::MAX),
        None
    );
    assert_eq!(graphs[5].roots.len(), 2);
    for (slot, raw) in [(0, "11"), (1, "44")] {
        assert_eq!(
            graphs[5].sequence_element(graphs[5].roots[slot], u64::MAX - 1),
            Some(&serde_json::json!(["int", 32, raw]))
        );
    }
    let nested_count = 5 * ((1u64 << 40) + 37);
    assert!(graphs[6].nodes.len() < 64);
    for index in [0, 1, 2, 3, 4, 5, nested_count - 1] {
        let raw = [22, 33, 11, 22, 11][(index % 5) as usize];
        assert_eq!(
            graphs[6].sequence_element(graphs[6].roots[0], index),
            Some(&serde_json::json!(["int", 32, raw.to_string()]))
        );
    }
    assert_eq!(
        graphs[6].sequence_element(graphs[6].roots[0], nested_count),
        None
    );
    assert_eq!(graphs[7].roots.len(), 2);
    for (index, raw) in [(0, "8"), (1, "9")] {
        assert_eq!(
            graphs[7].sequence_element(graphs[7].roots[0], index),
            Some(&serde_json::json!(["int", 32, raw]))
        );
    }
    assert_eq!(graphs[7].sequence_element(graphs[7].roots[0], 2), None);
    assert_eq!(graphs[7].sequence_element(graphs[7].roots[1], 0), None);
}

#[test]
fn compact_graph_shared_dags_and_deep_lists_validate_without_recursion() {
    use serde_json::json;
    let mut nodes = vec![json!(["int", 32, "7"]), json!(["uniform", "1", 0])];
    let mut tree = 1;
    for _ in 0..63 {
        nodes.push(json!(["concat", tree, tree]));
        tree = nodes.len() - 1;
    }
    nodes.push(json!(["array", (1u64 << 63).to_string(), tree]));
    let root = nodes.len() - 1;
    let j = json!({"graph":{"version":2,"nodes":nodes,"roots":[root]}});
    let g = Graph::decode(&j).unwrap();
    assert_eq!(g.nodes.len(), 66);
    for index in [0, 1, (1u64 << 63) - 1] {
        assert_eq!(g.sequence_element(root, index), Some(&g.nodes[0]));
    }
    assert_eq!(g.sequence_element(root, 1u64 << 63), None);

    let mut nodes = vec![json!(["int", 32, "7"]), json!(["nil"])];
    let mut list = 1;
    for _ in 0..10_000 {
        nodes.push(json!(["cons", 0, list]));
        list = nodes.len() - 1;
    }
    nodes.push(json!(["dense", list]));
    let tree = nodes.len() - 1;
    nodes.push(json!(["array", "10000", tree]));
    let root = nodes.len() - 1;
    let g = Graph::decode(&json!({"graph":{"version":2,"nodes":nodes,"roots":[root]}})).unwrap();
    assert_eq!(g.sequence_element(root, 9999), Some(&g.nodes[0]));
    assert_eq!(g.sequence_element(root, 10000), None);
}

#[test]
fn compact_graph_consumes_compiled_lean_physical_sharing_corpus() {
    use serde_json::json;
    use std::process::Command;
    if matches!(super::oracle(), super::Oracle::Absent) {
        return;
    }
    let lake = super::find_lake().expect("built oracle has lake");
    let build = super::lake_build_command(&lake, &super::lean_dir(), "trustir_observation_sharing")
        .output()
        .expect("build compiled sharing corpus");
    assert!(
        build.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let output =
        Command::new(super::lean_dir().join(".lake/build/bin/trustir_observation_sharing"))
            .arg("--corpus")
            .output()
            .expect("run compiled sharing corpus");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let rows: Vec<Json> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(rows.len(), 3);
    let graphs: Vec<Graph> = rows
        .iter()
        .map(|row| Graph::decode(&row["observation"]).unwrap())
        .collect();
    assert!(rows[0]["treeVisits"].as_u64().unwrap() <= 128);
    assert!(rows[0]["hits"].as_u64().unwrap() >= 63);
    assert!(graphs[0].nodes().len() < 256);
    let count = 1u64 << 63;
    let expected = Graph::decode(&json!({"graph":{"version":2,"nodes":[
        ["int",32,"7"], ["uniform",count.to_string(),0], ["array",count.to_string(),1],
        ["int",32,"99"], ["uniform",(count-1).to_string(),0], ["uniform","1",3],
        ["concat",4,5], ["array",count.to_string(),6]
    ],"roots":[2,7,2]}}))
    .unwrap();
    assert!(
        super::compact_graph_compare::equivalent(&graphs[0], &expected)
            .unwrap()
            .equal,
        "compiled source cache must preserve complete array contents"
    );
    for (slot, &root) in graphs[0].roots().iter().enumerate() {
        for index in [0, count / 2, count - 1] {
            let expected = if slot == 1 && index == count - 1 {
                "99"
            } else {
                "7"
            };
            assert_eq!(
                graphs[0].sequence_element(root, index),
                Some(&json!(["int", 32, expected]))
            );
        }
        assert!(graphs[0].sequence_element(root, count).is_none());
    }
    assert!(rows[1]["visits"].as_u64().unwrap() <= 328);
    assert!(graphs[1].nodes().len() <= 328);
    let mut nodes = vec![json!(["int", 32, "7"]), json!(["nil"])];
    let mut value = 0;
    for _ in 0..80 {
        let tail = nodes.len();
        nodes.push(json!(["cons", value, 1]));
        let head = nodes.len();
        nodes.push(json!(["cons", value, tail]));
        value = nodes.len();
        nodes.push(json!(["aggregate", head]));
    }
    let expected =
        Graph::decode(&json!({"graph":{"version":2,"nodes":nodes,"roots":[value,value]}})).unwrap();
    assert!(
        super::compact_graph_compare::equivalent(&graphs[1], &expected)
            .unwrap()
            .equal,
        "compiled source cache must preserve complete nested values"
    );
    assert_eq!(graphs[2].roots().len(), 21);
    assert_eq!(graphs[2].roots()[11], graphs[2].roots()[12]);
}
