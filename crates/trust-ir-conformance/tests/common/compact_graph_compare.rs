// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact equality of validated reference observations. Sequence words use the
//! interpreter's structural rope engine; nested value obligations use a work
//! list, not Rust recursion or logical array enumeration. This is not proof
//! evidence or an admitted original-execution operation.

use super::compact_value_graph::Graph;
use serde_json::Value as Json;
use std::collections::HashSet;
use trust_ir::interpret::ObservationWord;

#[derive(Debug, Default)]
pub(super) struct Comparison {
    pub(super) equal: bool,
    pub(super) value_pairs: usize,
    pub(super) word_comparisons: usize,
    pub(super) atom_checks: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Ref {
    side: usize,
    node: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Domain {
    Value,
    Fields,
}

fn index(j: &Json) -> usize {
    j.as_u64().expect("validated reference") as usize
}
fn tag(j: &Json) -> &str {
    j[0].as_str().expect("validated node tag")
}

fn build_words(graph: &Graph, offset: u64) -> Result<Vec<Option<ObservationWord>>, String> {
    let mut words: Vec<Option<ObservationWord>> = Vec::with_capacity(graph.nodes().len());
    for n in graph.nodes() {
        let prior = |j: &Json| words[index(j)].as_ref().expect("validated sequence edge");
        let symbol = |j: &Json| {
            offset
                .checked_add(j.as_u64().expect("validated value reference"))
                .ok_or_else(|| "observation symbol index overflow".to_owned())
        };
        let word = match tag(n) {
            "nil" | "empty" => Some(ObservationWord::empty()),
            "cons" => Some(
                ObservationWord::uniform(symbol(&n[1])?, 1)
                    .concat(prior(&n[2]))
                    .map_err(|e| e.to_string())?,
            ),
            "uniform" => Some(ObservationWord::uniform(
                symbol(&n[2])?,
                n[1].as_str().unwrap().parse().unwrap(),
            )),
            "dense" => Some(prior(&n[1]).clone()),
            "repeat" => Some(
                prior(&n[1])
                    .repeat(n[2].as_str().unwrap().parse().unwrap())
                    .map_err(|e| e.to_string())?,
            ),
            "concat" => Some(
                prior(&n[1])
                    .concat(prior(&n[2]))
                    .map_err(|e| e.to_string())?,
            ),
            _ => None,
        };
        words.push(word);
    }
    Ok(words)
}

pub(super) fn equivalent(left: &Graph, right: &Graph) -> Result<Comparison, String> {
    let mut result = Comparison::default();
    if left.roots().len() != right.roots().len() {
        return Ok(result);
    }
    let left_len =
        u64::try_from(left.nodes().len()).map_err(|_| "observation index domain overflow")?;
    left_len
        .checked_add(
            u64::try_from(right.nodes().len()).map_err(|_| "observation index domain overflow")?,
        )
        .ok_or("observation symbol domain overflow")?;
    let graphs = [left, right];
    let words = [build_words(left, 0)?, build_words(right, left_len)?];
    let mut pending = left
        .roots()
        .iter()
        .zip(right.roots())
        .map(|(&a, &b)| {
            (
                Domain::Value,
                Ref { side: 0, node: a },
                Ref { side: 1, node: b },
            )
        })
        .collect::<Vec<_>>();
    let mut seen = HashSet::new();
    while let Some((domain, a_ref, b_ref)) = pending.pop() {
        if a_ref == b_ref || !seen.insert((domain, a_ref, b_ref)) {
            continue;
        }
        let a = &graphs[a_ref.side].nodes()[a_ref.node];
        let b = &graphs[b_ref.side].nodes()[b_ref.node];
        // The existing W5b policy observes arrays and positional aggregates
        // by ordered contents. Lean's ordinary dense array value is an
        // aggregate; compact arrays carry an explicit length already checked
        // by the reader against their word. This is not nominal type equality.
        let positional = |t: &str| matches!(t, "array" | "aggregate");
        if tag(a) != tag(b)
            && !(domain == Domain::Value && positional(tag(a)) && positional(tag(b)))
        {
            return Ok(result);
        }
        let child = |parent: Ref, j: &Json| Ref {
            side: parent.side,
            node: index(j),
        };
        if domain == Domain::Fields {
            match tag(a) {
                "nil" => continue,
                "field" => {
                    if a[1] != b[1] {
                        return Ok(result);
                    }
                    pending.push((Domain::Value, child(a_ref, &a[2]), child(b_ref, &b[2])));
                    pending.push((Domain::Fields, child(a_ref, &a[3]), child(b_ref, &b[3])));
                    continue;
                }
                _ => return Err("unexpected validated field-list node".into()),
            }
        }
        result.value_pairs += 1;
        let sequence = match tag(a) {
            "int" | "float" | "bool" | "ptr" | "function" | "frame" | "poison" | "uninit" => {
                if a != b {
                    return Ok(result);
                }
                continue;
            }
            "fatptr" => {
                for i in [1, 2] {
                    pending.push((Domain::Value, child(a_ref, &a[i]), child(b_ref, &b[i])));
                }
                continue;
            }
            "record" => {
                pending.push((Domain::Fields, child(a_ref, &a[1]), child(b_ref, &b[1])));
                continue;
            }
            "array" => {
                if tag(b) == "array" && a[1] != b[1] {
                    return Ok(result);
                }
                2
            }
            "aggregate" | "vector" | "sequence" | "set" => 1,
            "closure" => {
                if a[1] != b[1] {
                    return Ok(result);
                }
                2
            }
            _ => return Err("unexpected validated value node".into()),
        };
        result.word_comparisons += 1;
        let a_word = words[a_ref.side][index(&a[sequence])]
            .as_ref()
            .expect("validated sequence");
        let b_sequence = if tag(b) == "array" {
            2
        } else if tag(a) == "array" {
            1
        } else {
            sequence
        };
        let b_word = words[b_ref.side][index(&b[b_sequence])]
            .as_ref()
            .expect("validated sequence");
        let same = a_word.equivalent_by(b_word, |x, y| {
            result.atom_checks += 1;
            let decode = |s: u64| {
                if s < left_len {
                    Ref {
                        side: 0,
                        node: s as usize,
                    }
                } else {
                    Ref {
                        side: 1,
                        node: (s - left_len) as usize,
                    }
                }
            };
            // This provisional true only records an obligation. Equality is
            // returned after every queued value pair has been checked. The
            // same word-engine control flow is valid once all its queried
            // atom equalities hold; a failed obligation rejects the batch.
            pending.push((Domain::Value, decode(x), decode(y)));
            true
        });
        if !same {
            return Ok(result);
        }
    }
    result.equal = true;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn graph(nodes: Vec<Json>, roots: Vec<usize>) -> Graph {
        Graph::decode(&json!({"graph":{"version":2,"nodes":nodes,"roots":roots}})).unwrap()
    }
    fn uniform(raw: u64) -> Graph {
        graph(
            vec![
                json!(["int", 32, raw.to_string()]),
                json!(["uniform", u64::MAX.to_string(), 0]),
                json!(["array", u64::MAX.to_string(), 1]),
            ],
            vec![2],
        )
    }
    fn last(raw: u64) -> Graph {
        graph(
            vec![
                json!(["int", 32, "7"]),
                json!(["int", 32, raw.to_string()]),
                json!(["uniform", (u64::MAX - 1).to_string(), 0]),
                json!(["uniform", "1", 1]),
                json!(["concat", 2, 3]),
                json!(["array", u64::MAX.to_string(), 4]),
            ],
            vec![5],
        )
    }

    #[test]
    fn graph_comparison_proves_huge_cross_shape_and_late_scalar_mismatch() {
        let a = uniform(7);
        let b = last(7);
        let equal = equivalent(&a, &b).unwrap();
        assert!(equal.equal);
        assert!(equal.atom_checks < 16);
        let bad = last(42);
        assert!(
            !equivalent(&a, &bad).unwrap().equal,
            "late scalar obligation must be checked"
        );
        let a = last(42);
        let b = last(42);
        assert!(equivalent(&a, &b).unwrap().equal);
        assert!(
            !equivalent(&a, &last(43)).unwrap().equal,
            "late scalar obligation must be checked"
        );
        assert!(!equivalent(&uniform(7), &uniform(8)).unwrap().equal);
    }

    fn periodic(values: &[u64], len: u64, tag_name: &str) -> Graph {
        let mut nodes = vec![json!(["nil"])];
        let mut ids = Vec::new();
        for &v in values {
            nodes.push(json!(["int", 32, v.to_string()]));
            ids.push(nodes.len() - 1);
        }
        let mut list = 0;
        for &value in ids.iter().rev() {
            nodes.push(json!(["cons", value, list]));
            list = nodes.len() - 1;
        }
        nodes.push(json!(["dense", list]));
        let unit = nodes.len() - 1;
        nodes.push(json!([
            "repeat",
            unit,
            (len / values.len() as u64).to_string()
        ]));
        let tree = nodes.len() - 1;
        nodes.push(if tag_name == "array" {
            json!([tag_name, len.to_string(), tree])
        } else {
            json!([tag_name, tree])
        });
        let root = nodes.len() - 1;
        graph(nodes, vec![root])
    }

    #[test]
    fn graph_comparison_handles_periods_and_list_tree_collection_forms() {
        let len = 4 * (u32::MAX as u64 / 4);
        for tag_name in ["array", "vector", "sequence", "set"] {
            let a = periodic(&[0, 1], len, tag_name);
            let b = periodic(&[0, 1, 0, 1], len, tag_name);
            let compared = equivalent(&a, &b).unwrap();
            assert!(compared.equal);
            assert!(compared.atom_checks < 32);
            assert!(
                !equivalent(&a, &periodic(&[0, 1, 0, 2], len, tag_name))
                    .unwrap()
                    .equal
            );
        }
        for tag_name in ["vector", "sequence", "set"] {
            let list = graph(
                vec![
                    json!(["int", 32, "7"]),
                    json!(["nil"]),
                    json!(["cons", 0, 1]),
                    json!(["cons", 0, 2]),
                    json!([tag_name, 3]),
                ],
                vec![4],
            );
            let tree = graph(
                vec![
                    json!(["int", 32, "7"]),
                    json!(["uniform", "2", 0]),
                    json!([tag_name, 1]),
                ],
                vec![2],
            );
            assert!(equivalent(&list, &tree).unwrap().equal);
        }
        assert!(
            !equivalent(
                &periodic(&[0, 1], len, "vector"),
                &periodic(&[0, 1], len, "sequence")
            )
            .unwrap()
            .equal
        );
    }

    fn compound_wire() -> Json {
        json!({"graph":{"version":2,"nodes":[
            ["int",32,"7"],["bool",true],["ptr",true],["nil"],["cons",0,3],["field","a",0,3],
            ["closure",4,4],["record",5],["fatptr",2,0],["function",1,2],["frame",1],
            ["poison"],["uninit"],["float","nan"],["aggregate",4],["vector",4],["sequence",4],["set",4],
            ["uniform","1",0],["array","1",18]
        ],"roots":[0,1,2,6,7,8,9,10,11,12,13,14,15,16,17,19]}})
    }

    #[test]
    fn graph_comparison_checks_compound_metadata_root_order_and_renumbering() {
        let original = compound_wire();
        let a = Graph::decode(&original).unwrap();
        assert!(equivalent(&a, &a).unwrap().equal);
        for (node, field, replacement) in [
            (0, 2, json!("8")),
            (1, 1, json!(false)),
            (2, 1, json!(false)),
            (6, 1, json!(5)),
            (5, 1, json!("b")),
            (9, 1, json!(2)),
            (9, 2, json!(3)),
            (10, 1, json!(2)),
            (13, 1, json!("0")),
        ] {
            let mut changed = original.clone();
            changed["graph"]["nodes"][node][field] = replacement;
            assert!(
                !equivalent(&a, &Graph::decode(&changed).unwrap())
                    .unwrap()
                    .equal,
                "all compound metadata must be checked: node {node}"
            );
        }
        let mut changed = original.clone();
        changed["graph"]["nodes"][11] = json!(["uninit"]);
        assert!(
            !equivalent(&a, &Graph::decode(&changed).unwrap())
                .unwrap()
                .equal
        );
        let mut changed = original.clone();
        changed["graph"]["roots"].as_array_mut().unwrap().reverse();
        assert!(
            !equivalent(&a, &Graph::decode(&changed).unwrap())
                .unwrap()
                .equal
        );
        let mut changed = original.clone();
        changed["graph"]["roots"]
            .as_array_mut()
            .unwrap()
            .push(json!(0));
        assert!(
            !equivalent(&a, &Graph::decode(&changed).unwrap())
                .unwrap()
                .equal
        );
        // Change only storage indices, including closure and field edges;
        // function/signature ids and frame counts are metadata, not edges.
        let mut nodes = vec![json!(["bool", false])];
        for n in original["graph"]["nodes"].as_array().unwrap() {
            let mut n = n.clone();
            let edges: &[usize] = match tag(&n) {
                "cons" | "fatptr" | "concat" => &[1, 2],
                "field" => &[2, 3],
                "closure" | "array" | "uniform" => &[2],
                "record" | "aggregate" | "vector" | "sequence" | "set" | "dense" | "repeat" => &[1],
                _ => &[],
            };
            for &i in edges {
                n[i] = json!(index(&n[i]) + 1);
            }
            nodes.push(n);
        }
        let roots = a.roots().iter().map(|r| r + 1).collect();
        assert!(equivalent(&a, &graph(nodes, roots)).unwrap().equal);
    }

    fn deep(depth: usize, raw: u64) -> Graph {
        let mut nodes = vec![json!(["int", 32, raw.to_string()]), json!(["nil"])];
        let mut value = 0;
        for _ in 0..depth {
            nodes.push(json!(["cons", value, 1]));
            let tail = nodes.len() - 1;
            nodes.push(json!(["cons", value, tail]));
            let captures = nodes.len() - 1;
            nodes.push(json!(["closure", 4, captures]));
            value = nodes.len() - 1;
        }
        graph(nodes, vec![value, value])
    }

    #[test]
    fn graph_comparison_checks_deep_shared_values_without_recursive_descent() {
        let a = deep(10_000, 7);
        let b = deep(10_000, 7);
        let compared = equivalent(&a, &b).unwrap();
        assert!(compared.equal);
        assert_eq!(compared.value_pairs, 10_001);
        assert!(compared.atom_checks <= 20_000);
        assert!(
            !equivalent(&a, &deep(10_000, 8)).unwrap().equal,
            "deep scalar obligation must be checked"
        );
    }

    fn finite(values: &[u64], runs: bool) -> Graph {
        let mut nodes = (0..4)
            .map(|v| json!(["int", 32, v.to_string()]))
            .collect::<Vec<_>>();
        let content = if runs {
            nodes.push(json!(["empty"]));
            let mut tree = nodes.len() - 1;
            for &v in values {
                nodes.push(json!(["uniform", "1", v]));
                let leaf = nodes.len() - 1;
                nodes.push(json!(["concat", tree, leaf]));
                tree = nodes.len() - 1;
            }
            tree
        } else {
            nodes.push(json!(["nil"]));
            let mut list = nodes.len() - 1;
            for &v in values.iter().rev() {
                nodes.push(json!(["cons", v, list]));
                list = nodes.len() - 1;
            }
            nodes.push(json!(["dense", list]));
            nodes.len() - 1
        };
        nodes.push(json!(["array", values.len().to_string(), content]));
        let root = nodes.len() - 1;
        graph(nodes, vec![root])
    }

    #[test]
    fn graph_comparison_matches_independent_finite_sequence_equality() {
        let inputs = (0..64u64)
            .map(|seed| {
                (0..(seed % 9))
                    .map(|i| (seed >> (i % 6)) & 3)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let dense = inputs.iter().map(|v| finite(v, false)).collect::<Vec<_>>();
        let runs = inputs.iter().map(|v| finite(v, true)).collect::<Vec<_>>();
        for (i, a) in dense.iter().enumerate() {
            for (j, b) in runs.iter().enumerate() {
                assert_eq!(
                    equivalent(a, b).unwrap().equal,
                    inputs[i] == inputs[j],
                    "finite reference {i}/{j}"
                );
            }
        }
    }
}
