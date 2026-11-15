// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-result reference observations for the conformance harness. This is
//! not an admitted original-execution API and grants no proof authority.

use super::compact_value_graph::Graph;
use serde_json::{Value as Json, json};
use std::collections::HashMap;
use trust_ir::Ty;
use trust_ir::interpret::{
    ArrayNode, ArrayNodeKind, ArrayStructureId, InterpretValue, InterpretValueKind as K,
};

#[derive(Debug, Default)]
struct Stats {
    values: usize,
    tree_nodes: usize,
    tree_hits: usize,
}

#[derive(Debug)]
struct Collection {
    graph: Graph,
    stats: Stats,
}

enum Cache<'a> {
    Value(usize),
    Tree(ArrayStructureId<'a>),
    None,
}

enum Make<'a> {
    Container(&'static str),
    Array(u64),
    FatPtr,
    Closure(u32),
    List,
    Fields(Vec<&'a str>),
    Dense,
    Uniform(u64),
    Repeat(u64),
    Concat,
}

enum Task<'a> {
    Value(&'a InterpretValue),
    Tree(Option<ArrayNode<'a>>),
    List(&'a [InterpretValue]),
    Fields(&'a [(String, InterpretValue)]),
    Finish {
        cache: Cache<'a>,
        make: Make<'a>,
        children: usize,
    },
}

#[derive(Default)]
struct Collector<'a> {
    nodes: Vec<Json>,
    canonical: HashMap<String, usize>,
    // Inputs remain borrowed throughout collection. No pointer is serialized
    // or dereferenced through an integer; the value map only recognizes the
    // same live, nonzero-sized immutable object before traversing its fields.
    values: HashMap<usize, Option<usize>>,
    trees: HashMap<ArrayStructureId<'a>, Option<usize>>,
    stats: Stats,
}

impl<'a> Collector<'a> {
    fn intern(&mut self, node: Json) -> usize {
        let key = node.to_string();
        if let Some(&id) = self.canonical.get(&key) {
            return id;
        }
        let id = self.nodes.len();
        self.nodes.push(node);
        self.canonical.insert(key, id);
        id
    }

    fn finish(&mut self, make: Make<'_>, ids: Vec<usize>) -> usize {
        match make {
            Make::Container(tag) => self.intern(json!([tag, ids[0]])),
            Make::Array(len) => self.intern(json!(["array", len.to_string(), ids[0]])),
            Make::FatPtr => self.intern(json!(["fatptr", ids[0], ids[1]])),
            Make::Closure(func) => self.intern(json!(["closure", func, ids[0]])),
            Make::Dense => self.intern(json!(["dense", ids[0]])),
            Make::Uniform(len) => self.intern(json!(["uniform", len.to_string(), ids[0]])),
            Make::Repeat(count) => self.intern(json!(["repeat", ids[0], count.to_string()])),
            Make::Concat => self.intern(json!(["concat", ids[0], ids[1]])),
            Make::List => {
                let mut tail = self.intern(json!(["nil"]));
                for id in ids.into_iter().rev() {
                    tail = self.intern(json!(["cons", id, tail]));
                }
                tail
            }
            Make::Fields(names) => {
                let mut tail = self.intern(json!(["nil"]));
                for (name, id) in names.into_iter().zip(ids).rev() {
                    tail = self.intern(json!(["field", name, id, tail]));
                }
                tail
            }
        }
    }

    fn collect(mut self, roots: &'a [InterpretValue]) -> Result<Collection, String> {
        let mut pending: Vec<_> = roots.iter().rev().map(Task::Value).collect();
        let mut output = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                Task::Value(value) => {
                    let key = value as *const InterpretValue as usize;
                    if let Some(cached) = self.values.get(&key) {
                        output.push(cached.ok_or("cyclic value observation")?);
                        continue;
                    }
                    self.values.insert(key, None);
                    self.stats.values += 1;
                    let cache = Cache::Value(key);
                    let scalar = match &value.kind {
                        K::Int(i) => Some(json!(["int", i.bits, i.raw.to_string()])),
                        K::Bool(b) => Some(json!(["bool", b])),
                        K::FloatBits(bits) => {
                            let f = match value.ty {
                                Ty::F16 => trust_ir::interpret::f16_bits_to_f64(*bits as u16),
                                Ty::F32 => f64::from(f32::from_bits(*bits as u32)),
                                _ => f64::from_bits(*bits),
                            };
                            Some(json!([
                                "float",
                                if f.is_nan() {
                                    "nan".to_owned()
                                } else {
                                    f.to_bits().to_string()
                                }
                            ]))
                        }
                        K::Ptr(_) | K::DanglingPtr(_) => Some(json!(["ptr", false])),
                        K::NullPtr => Some(json!(["ptr", true])),
                        K::Frame { slots, .. } => Some(json!(["frame", slots.len()])),
                        K::PartialBytes(_) => Some(json!(["poison"])),
                        K::Uninit => Some(json!(["uninit"])),
                        K::FnDef(func) => {
                            let Ty::Func(sig) = value.ty else {
                                return Err("function observation has no function signature".into());
                            };
                            Some(json!(["function", sig.0, func.0]))
                        }
                        K::Handle { .. } => {
                            return Err("host handles have no Lean value observation".into());
                        }
                        K::Tensor { .. } => {
                            return Err("tensor values have no W5b Lean value observation".into());
                        }
                        K::Array(array) | K::Vector(array) | K::Sequence(array) | K::Set(array) => {
                            let make = match &value.kind {
                                K::Array(_) => Make::Array(array.len()),
                                K::Vector(_) => Make::Container("vector"),
                                K::Sequence(_) => Make::Container("sequence"),
                                K::Set(_) => Make::Container("set"),
                                _ => unreachable!(),
                            };
                            pending.push(Task::Finish {
                                cache,
                                make,
                                children: 1,
                            });
                            pending.push(Task::Tree(array.root_node()));
                            None
                        }
                        K::Aggregate(values) => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::Container("aggregate"),
                                children: 1,
                            });
                            pending.push(Task::List(values));
                            None
                        }
                        K::Unit | K::PhantomData => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::Container("aggregate"),
                                children: 1,
                            });
                            pending.push(Task::List(&[]));
                            None
                        }
                        K::Record(fields) => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::Container("record"),
                                children: 1,
                            });
                            pending.push(Task::Fields(fields));
                            None
                        }
                        K::Closure { func, captures } => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::Closure(func.0),
                                children: 1,
                            });
                            pending.push(Task::List(captures));
                            None
                        }
                        K::FatPtr { data, metadata } => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::FatPtr,
                                children: 2,
                            });
                            pending.push(Task::Value(metadata));
                            pending.push(Task::Value(data));
                            None
                        }
                    };
                    if let Some(node) = scalar {
                        let id = self.intern(node);
                        self.values.insert(key, Some(id));
                        output.push(id);
                    }
                }
                Task::Tree(None) => {
                    let id = self.intern(json!(["empty"]));
                    output.push(id);
                }
                Task::Tree(Some(node)) => {
                    let key = node.id();
                    if let Some(cached) = self.trees.get(&key) {
                        output.push(cached.ok_or("cyclic array observation")?);
                        self.stats.tree_hits += 1;
                        continue;
                    }
                    self.trees.insert(key, None);
                    self.stats.tree_nodes += 1;
                    let cache = Cache::Tree(key);
                    // The global memo lookup precedes kind(): no eager
                    // snapshot or child walk occurs for an already seen node.
                    match node.kind() {
                        ArrayNodeKind::Dense(values) => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::Dense,
                                children: 1,
                            });
                            pending.push(Task::List(values));
                        }
                        ArrayNodeKind::Uniform(value) => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::Uniform(node.len()),
                                children: 1,
                            });
                            pending.push(Task::Value(value));
                        }
                        ArrayNodeKind::Repeat { unit, count } => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::Repeat(count),
                                children: 1,
                            });
                            pending.push(Task::Tree(Some(unit)));
                        }
                        ArrayNodeKind::Concat { left, right } => {
                            pending.push(Task::Finish {
                                cache,
                                make: Make::Concat,
                                children: 2,
                            });
                            pending.push(Task::Tree(Some(right)));
                            pending.push(Task::Tree(Some(left)));
                        }
                    }
                }
                Task::List(values) => {
                    pending.push(Task::Finish {
                        cache: Cache::None,
                        make: Make::List,
                        children: values.len(),
                    });
                    pending.extend(values.iter().rev().map(Task::Value));
                }
                Task::Fields(fields) => {
                    pending.push(Task::Finish {
                        cache: Cache::None,
                        make: Make::Fields(fields.iter().map(|(n, _)| n.as_str()).collect()),
                        children: fields.len(),
                    });
                    pending.extend(fields.iter().rev().map(|(_, v)| Task::Value(v)));
                }
                Task::Finish {
                    cache,
                    make,
                    children,
                } => {
                    let start = output
                        .len()
                        .checked_sub(children)
                        .ok_or("observation result stack underflow")?;
                    let ids = output.split_off(start);
                    let id = self.finish(make, ids);
                    match cache {
                        Cache::Value(key) => {
                            self.values.insert(key, Some(id));
                        }
                        Cache::Tree(key) => {
                            self.trees.insert(key, Some(id));
                        }
                        Cache::None => {}
                    }
                    output.push(id);
                }
            }
        }
        if output.len() != roots.len() {
            return Err("observation root stack mismatch".into());
        }
        let wire = json!({"graph":{"version":2,"nodes":self.nodes,"roots":output}});
        let graph = Graph::decode(&wire)?;
        Ok(Collection {
            graph,
            stats: self.stats,
        })
    }
}

pub(super) fn observe(roots: &[InterpretValue]) -> Result<Graph, String> {
    collect(roots).map(|collection| collection.graph)
}

fn collect(roots: &[InterpretValue]) -> Result<Collection, String> {
    Collector::default().collect(roots)
}

fn value(ty: Ty, kind: K) -> InterpretValue {
    InterpretValue { ty, kind }
}
fn int(n: u64) -> InterpretValue {
    InterpretValue::int(Ty::U32, n as i128).unwrap()
}
fn array(a: trust_ir::interpret::ArrayValue) -> InterpretValue {
    value(
        Ty::Array(trust_ir::value::TyId::new(0), a.len()),
        K::Array(a),
    )
}

#[test]
fn whole_graph_collects_nested_huge_collections_and_shared_roots() {
    use trust_ir::interpret::ArrayValue;
    use trust_ir::value::{ClosureTyId, FuncId, RecordId, TyId};
    let shared = ArrayValue::splat(int(7), u64::MAX);
    let a = array(shared.clone());
    let nested = value(
        Ty::Array(TyId::new(2), u64::MAX),
        K::Array(ArrayValue::splat(a.clone(), u64::MAX)),
    );
    let vector = value(
        Ty::Vector(Box::new(Ty::U32), u32::MAX),
        K::Vector(ArrayValue::splat(int(7), u32::MAX.into())),
    );
    let sequence = value(Ty::Sequence(TyId::new(0)), K::Sequence(shared.clone()));
    let set = value(
        Ty::Set(TyId::new(0), trust_ir::ty::SetRepr::Boxed),
        K::Set(shared),
    );
    let record = value(
        Ty::Record(RecordId::new(0)),
        K::Record(vec![
            ("array".into(), a.clone()),
            ("sequence".into(), sequence.clone()),
        ]),
    );
    let closure = value(
        Ty::Closure(ClosureTyId::new(0)),
        K::Closure {
            func: FuncId::new(4),
            captures: vec![nested.clone(), a.clone()],
        },
    );
    let roots = vec![
        a,
        vector,
        sequence,
        set,
        nested,
        record,
        closure.clone(),
        closure,
    ];
    let c = collect(&roots).unwrap();
    assert_eq!(c.stats.tree_nodes, 3);
    assert!(c.stats.tree_hits >= 5);
    assert!(c.stats.values < 64 && c.graph.nodes().len() < 64);
    assert_eq!(c.graph.roots().len(), 8);
    assert_eq!(c.graph.roots()[6], c.graph.roots()[7]);
    for (slot, len, tag) in [
        (0, u64::MAX, "array"),
        (1, u32::MAX.into(), "vector"),
        (2, u64::MAX, "sequence"),
        (3, u64::MAX, "set"),
    ] {
        let root = c.graph.roots()[slot];
        assert_eq!(c.graph.nodes()[root][0], tag);
        for index in [0, len - 1] {
            assert_eq!(
                c.graph.sequence_element(root, index),
                Some(&json!(["int", 32, "7"]))
            );
        }
        assert_eq!(c.graph.sequence_element(root, len), None);
    }
    assert_eq!(
        c.graph.sequence_element(c.graph.roots()[4], u64::MAX - 1),
        Some(&c.graph.nodes()[c.graph.roots()[0]])
    );
    let record = &c.graph.nodes()[c.graph.roots()[5]];
    let mut fields = record[1].as_u64().unwrap() as usize;
    for (name, root) in [
        ("array", c.graph.roots()[0]),
        ("sequence", c.graph.roots()[2]),
    ] {
        let field = &c.graph.nodes()[fields];
        assert_eq!(field[0], "field");
        assert_eq!(
            field[1], name,
            "record field names must preserve source order"
        );
        assert_eq!(field[2], root);
        fields = field[3].as_u64().unwrap() as usize;
    }
    assert_eq!(c.graph.nodes()[fields], json!(["nil"]));
    let closure = &c.graph.nodes()[c.graph.roots()[6]];
    let mut captures = closure[2].as_u64().unwrap() as usize;
    for root in [c.graph.roots()[4], c.graph.roots()[0]] {
        let cons = &c.graph.nodes()[captures];
        assert_eq!(cons[0], "cons");
        assert_eq!(cons[1], root);
        captures = cons[2].as_u64().unwrap() as usize;
    }
    assert_eq!(c.graph.nodes()[captures], json!(["nil"]));
}

#[test]
fn whole_graph_overlapping_batches_visit_each_stored_tree_once() {
    use std::collections::HashSet;
    use trust_ir::interpret::ArrayValue;
    let mut arrays = vec![ArrayValue::from_vec((0..4096).map(int).collect())];
    for n in 0..1024 {
        arrays.push(arrays.last().unwrap().set(0, int(100_000 + n)).unwrap());
    }
    arrays.push(arrays[0].clone());
    let expected = arrays
        .iter()
        .flat_map(|a| a.structure().identities)
        .collect::<HashSet<_>>()
        .len();
    let roots = arrays.into_iter().map(array).collect::<Vec<_>>();
    let c = collect(&roots).unwrap();
    assert_eq!(
        c.stats.tree_nodes, expected,
        "whole-result tree visits must match physical union"
    );
    assert_eq!(expected, 9727);
    assert!(c.graph.nodes().len() < 30_000);
    assert_eq!(c.graph.roots().len(), 1026);
    for (i, &root) in c.graph.roots().iter().enumerate() {
        let first = if i == 0 || i == 1025 {
            0
        } else {
            100_000 + i - 1
        };
        for (index, raw) in [(0, first), (1, 1), (4095, 4095)] {
            assert_eq!(
                c.graph.sequence_element(root, index),
                Some(&json!(["int", 32, raw.to_string()]))
            );
        }
        assert_eq!(c.graph.sequence_element(root, 4096), None);
    }
    println!(
        "whole result collection: 1026 roots; {} tree visits; {} tree cache hits; {} wire nodes",
        c.stats.tree_nodes,
        c.stats.tree_hits,
        c.graph.nodes().len()
    );
}

#[test]
fn whole_graph_preserves_dense_periods_and_updates() {
    use trust_ir::interpret::ArrayValue;
    use trust_ir::value::TyId;
    let dense = ArrayValue::from_vec((0..65).map(int).collect());
    let periodic = dense.repeat(u64::MAX / 65);
    let last = periodic.len() - 1;
    let changed = last - 7;
    let updated = periodic.set(changed, int(999)).unwrap();
    let roots = vec![
        array(dense.clone()),
        array(periodic),
        array(updated),
        value(Ty::Vector(Box::new(Ty::U32), 65), K::Vector(dense.clone())),
        value(Ty::Sequence(TyId::new(0)), K::Sequence(dense.clone())),
        value(
            Ty::Set(TyId::new(0), trust_ir::ty::SetRepr::Boxed),
            K::Set(dense),
        ),
    ];
    let c = collect(&roots).unwrap();
    for slot in [0, 3, 4, 5] {
        for i in 0..65 {
            assert_eq!(
                c.graph.sequence_element(c.graph.roots()[slot], i),
                Some(&json!(["int", 32, i.to_string()]))
            );
        }
        assert_eq!(c.graph.sequence_element(c.graph.roots()[slot], 65), None);
    }
    for slot in [1, 2] {
        for i in (0..130).chain([changed - 1, changed, changed + 1, last, last + 1]) {
            let expected = if i > last {
                None
            } else {
                Some(json!([
                    "int",
                    32,
                    if slot == 2 && i == changed {
                        "999".into()
                    } else {
                        (i % 65).to_string()
                    }
                ]))
            };
            assert_eq!(
                c.graph.sequence_element(c.graph.roots()[slot], i),
                expected.as_ref()
            );
        }
    }
}

#[test]
fn whole_graph_handles_deep_captures_and_refuses_unrepresentable_values() {
    let empty = collect(&[]).unwrap();
    assert!(empty.graph.roots().is_empty() && empty.graph.nodes().is_empty());
    use trust_ir::value::{ClosureTyId, FuncId};
    let mut root = int(7);
    for n in 0..10_000 {
        root = value(
            Ty::Closure(ClosureTyId::new(n)),
            K::Closure {
                func: FuncId::new(n),
                captures: vec![root],
            },
        );
    }
    let roots = vec![root];
    let result = collect(&roots);
    // Retire this deliberately deep owned fixture iteratively as well. The
    // collector borrows inputs and has no recursive ownership of their data.
    let mut retire = roots;
    while let Some(v) = retire.pop() {
        if let K::Closure { captures, .. } = v.kind {
            retire.extend(captures);
        }
    }
    let c = result.unwrap();
    assert_eq!(c.stats.values, 10_001);
    assert_eq!(c.stats.tree_nodes, 0);
    let mut at = c.graph.roots()[0];
    for n in (0..10_000).rev() {
        let node = &c.graph.nodes()[at];
        assert_eq!(node[0], "closure");
        assert_eq!(node[1], n);
        let captures = node[2].as_u64().unwrap() as usize;
        let cons = &c.graph.nodes()[captures];
        assert_eq!(cons[0], "cons");
        let tail = cons[2].as_u64().unwrap() as usize;
        assert_eq!(c.graph.nodes()[tail], json!(["nil"]));
        at = cons[1].as_u64().unwrap() as usize;
    }
    assert_eq!(c.graph.nodes()[at], json!(["int", 32, "7"]));
    let handle = value(
        Ty::Handle(Box::new(trust_ir::ty::HandleTy::new("File", "test"))),
        K::Handle { id: 1 },
    );
    assert!(
        collect(std::slice::from_ref(&handle))
            .unwrap_err()
            .contains("host handles")
    );
    // The W5b Lean model has no tensor value: refused, never flattened.
    let tensor = value(
        Ty::Tensor(Box::new(Ty::U32), 1),
        K::Tensor {
            dims: vec![1],
            elems: trust_ir::interpret::ArrayValue::from_vec(vec![int(7)]),
        },
    );
    assert!(
        collect(std::slice::from_ref(&tensor))
            .unwrap_err()
            .contains("tensor values")
    );
    let frame = value(
        Ty::Ptr,
        K::Frame {
            lineage: 1,
            slots: std::sync::Arc::from(vec![Some(handle)]),
        },
    );
    let c = collect(&[frame]).unwrap();
    assert_eq!(c.graph.nodes()[c.graph.roots()[0]], json!(["frame", 1]));
    let invalid = value(Ty::U32, K::FnDef(FuncId::new(1)));
    assert!(collect(&[invalid]).unwrap_err().contains("signature"));
    let invalid = value(
        Ty::FatPtr(trust_ir::ty::FatPtrKind::Str),
        K::FatPtr {
            data: Box::new(int(1)),
            metadata: Box::new(int(2)),
        },
    );
    assert!(collect(&[invalid]).unwrap_err().contains("not a pointer"));
    let c = collect(&[
        value(Ty::Unit, K::Unit),
        value(Ty::Unit, K::PhantomData),
        value(Ty::F16, K::FloatBits(0x8000)),
        value(Ty::F32, K::FloatBits(1.5f32.to_bits().into())),
    ])
    .unwrap();
    assert_eq!(c.graph.roots()[0], c.graph.roots()[1]);
    assert_eq!(c.graph.nodes()[c.graph.roots()[0]][0], "aggregate");
    assert_eq!(
        c.graph.nodes()[c.graph.roots()[2]],
        json!(["float", (-0.0f64).to_bits().to_string()])
    );
    assert_eq!(
        c.graph.nodes()[c.graph.roots()[3]],
        json!(["float", 1.5f64.to_bits().to_string()])
    );
}

#[test]
fn whole_graph_collection_matches_live_lean_corpus_observations() {
    use trust_ir::interpret::ArrayValue;
    use trust_ir::value::{ClosureTyId, FuncId, FuncTyId, RecordId, TyId};
    let Some(rows) = super::compact_value_graph::lean_corpus() else {
        return;
    };
    assert_eq!(rows.len(), 8);
    let lean = rows
        .iter()
        .map(|j| Graph::decode(j).unwrap())
        .collect::<Vec<_>>();
    let uniform = ArrayValue::splat(int(7), u64::MAX);
    let array_value = array(uniform.clone());
    let mixed = vec![
        InterpretValue::int(Ty::I128, -1).unwrap(),
        InterpretValue::bool(true),
        value(Ty::F64, K::FloatBits(f64::NAN.to_bits())),
        value(Ty::F64, K::FloatBits((-0.0f64).to_bits())),
        value(Ty::Ptr, K::DanglingPtr(0)),
        value(Ty::Ptr, K::NullPtr),
        value(
            Ty::FatPtr(trust_ir::ty::FatPtrKind::Slice(TyId::new(0))),
            K::FatPtr {
                data: Box::new(value(Ty::Ptr, K::NullPtr)),
                metadata: Box::new(InterpretValue::int(Ty::U64, 9).unwrap()),
            },
        ),
        value(
            Ty::Tuple(vec![Ty::U32, Ty::U8]),
            K::Aggregate(vec![
                value(Ty::U32, K::Uninit),
                InterpretValue::int(Ty::U8, 255).unwrap(),
            ]),
        ),
        value(
            Ty::Vector(Box::new(Ty::Bool), 1),
            K::Vector(ArrayValue::from_vec(vec![InterpretValue::bool(false)])),
        ),
        value(
            Ty::Sequence(TyId::new(1)),
            K::Sequence(ArrayValue::from_vec(vec![
                InterpretValue::int(Ty::U16, 1).unwrap(),
            ])),
        ),
        value(
            Ty::Set(TyId::new(1), trust_ir::ty::SetRepr::Boxed),
            K::Set(ArrayValue::from_vec(vec![
                InterpretValue::int(Ty::U16, 2).unwrap(),
            ])),
        ),
        value(
            Ty::Record(RecordId::new(0)),
            K::Record(vec![("λ".into(), int(3))]),
        ),
        value(
            Ty::Closure(ClosureTyId::new(0)),
            K::Closure {
                func: FuncId::new(4),
                captures: vec![array_value.clone()],
            },
        ),
        value(
            Ty::Closure(ClosureTyId::new(5)),
            K::Closure {
                func: FuncId::new(4),
                captures: vec![array_value.clone()],
            },
        ),
        value(Ty::Func(FuncTyId::new(6)), K::FnDef(FuncId::new(7))),
        value(
            Ty::Ptr,
            K::Frame {
                lineage: 1,
                slots: std::sync::Arc::from(vec![None]),
            },
        ),
        value(Ty::U8, K::PartialBytes(vec![None])),
        value(Ty::U32, K::Uninit),
        array(ArrayValue::from_vec(vec![])),
    ];
    let periodic = ArrayValue::from_vec(vec![int(22), int(33), int(11)]).repeat(u64::MAX / 3);
    let batches = [
        vec![array_value],
        vec![array(uniform.set(u64::MAX - 1, int(42)).unwrap())],
        mixed,
        vec![array(ArrayValue::from_vec((0..65).map(int).collect()))],
        vec![array(periodic.clone())],
        vec![
            array(periodic.clone()),
            array(periodic.set(u64::MAX - 1, int(44)).unwrap()),
        ],
        vec![array(
            ArrayValue::from_vec(vec![int(22), int(33), int(11), int(22), int(11)])
                .repeat((1u64 << 40) + 37),
        )],
        vec![
            array(ArrayValue::from_vec(vec![int(8), int(9)])),
            array(ArrayValue::from_vec(vec![])),
        ],
    ];
    let rust = batches
        .iter()
        .map(|values| collect(values).unwrap().graph)
        .collect::<Vec<_>>();
    for row in [0, 1] {
        for index in [0, u64::MAX - 2, u64::MAX - 1, u64::MAX] {
            assert_eq!(
                rust[row].sequence_element(rust[row].roots()[0], index),
                lean[row].sequence_element(lean[row].roots()[0], index)
            );
        }
    }
    assert_eq!(rust[2].roots().len(), 19);
    for slot in [0, 1, 2, 3, 4, 5, 14, 15, 16, 17] {
        assert_eq!(
            rust[2].nodes()[rust[2].roots()[slot]],
            lean[2].nodes()[lean[2].roots()[slot]],
            "scalar root {slot}"
        );
    }
    for slot in [7, 8, 9, 10, 18] {
        for index in 0..3 {
            assert_eq!(
                rust[2].sequence_element(rust[2].roots()[slot], index),
                lean[2].sequence_element(lean[2].roots()[slot], index),
                "collection root {slot} index {index}"
            );
        }
    }
    for graph in [&rust[2], &lean[2]] {
        let fat = &graph.nodes()[graph.roots()[6]];
        assert_eq!(fat[0], "fatptr");
        assert_eq!(
            graph.nodes()[fat[1].as_u64().unwrap() as usize],
            json!(["ptr", true])
        );
        assert_eq!(
            graph.nodes()[fat[2].as_u64().unwrap() as usize],
            json!(["int", 64, "9"])
        );
        let record = &graph.nodes()[graph.roots()[11]];
        assert_eq!(record[0], "record");
        let field = &graph.nodes()[record[1].as_u64().unwrap() as usize];
        assert_eq!(field[0], "field");
        assert_eq!(field[1], "λ");
        assert_eq!(
            graph.nodes()[field[2].as_u64().unwrap() as usize],
            json!(["int", 32, "3"])
        );
        assert_eq!(
            graph.nodes()[field[3].as_u64().unwrap() as usize],
            json!(["nil"])
        );
        assert_eq!(graph.roots()[12], graph.roots()[13]);
        let closure = &graph.nodes()[graph.roots()[12]];
        assert_eq!(closure[0], "closure");
        assert_eq!(closure[1], 4);
        let captures = &graph.nodes()[closure[2].as_u64().unwrap() as usize];
        assert_eq!(captures[0], "cons");
        let captured = captures[1].as_u64().unwrap() as usize;
        assert_eq!(
            graph.sequence_element(captured, u64::MAX - 1),
            Some(&json!(["int", 32, "7"]))
        );
    }
    for index in 0..66 {
        assert_eq!(
            rust[3].sequence_element(rust[3].roots()[0], index),
            lean[3].sequence_element(lean[3].roots()[0], index)
        );
    }
    for row in 0..rust.len() {
        let compared = super::compact_graph_compare::equivalent(&rust[row], &lean[row]).unwrap();
        assert!(
            compared.equal,
            "entire live corpus graph {row} differs: {compared:?}"
        );
    }
}
