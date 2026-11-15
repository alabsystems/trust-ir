// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// ══════════════════════════════════════════════════════════════════════════
// Content-addressed weight blobs (PKG-U13e): `Constant::TensorBlob` and the
// module blob table in the builder, the validator, the merge, the binary
// codec, the body digest, the reference interpreter and the codegen gate
// (docs/SPEC_RATIFICATIONS.md §27).
// ══════════════════════════════════════════════════════════════════════════
//
// What this battery pins:
//
//   * identical bytes are stored once: interning them twice (in one module,
//     through the builder, and across a merge of two modules that both hold
//     them) leaves one table row, and the binary image carries the bytes once;
//   * the table's rules: a row whose bytes do not hash to its digest, rows out
//     of ascending order and a digest listed twice are `InvalidBlobTable`
//     (B2, B1), each with a reason that names its rule, and every decoder
//     refuses the same order;
//   * a constant whose digest names no row is `MissingBlob`;
//   * the constant's rules: placement (C1: a global initializer, a lane of an
//     aggregate), rank (C2), extents and element count below `2^pointer_bits`
//     at 64- and 32-bit pointer width (C3), and the row's byte count (C4),
//     each `InvalidTensorBlob` with a reason that names its rule; a float
//     element is the TYPE's refusal (`InvalidTensorType`), by name;
//   * the reference interpreter reads every integer element type, at ranks 0
//     to 3 and with zero extents, as the little-endian decode of the row's
//     bytes, in one fuel unit, and refuses every malformed shape as a
//     `TypeError` (an execution of a module the validator refuses);
//   * a function's body digest reads the digest the constant spells, never the
//     bytes: replacing a row's bytes, adding a row and dropping one leave it
//     unchanged while `stable_digest` moves, and naming another digest moves
//     it;
//   * the default codegen gate refuses the constant by name
//     (`UnlowerableForCodegen`): a tensor has no machine layout.

use trust_ir::blob::{Blob, BlobDigest};
use trust_ir::constant::Constant;
use trust_ir::ty::{ClosureTy, EnumDef, EnumVariant};
use trust_ir::value::EnumId;
use trust_ir::{
    Endianness, FuncId, Global, InterpretErrorCode, InterpretOutcome, InterpretResult,
    InterpretValueKind, Interpreter, Linkage, Module, TargetInfo, Ty,
};
use trust_ir_build::merge::{MergePolicy, merge_into};
use trust_ir_build::{
    FunctionBuilder, ModuleBuilder, ValidationError, validate_function, validate_module,
    validate_module_for_codegen,
};

fn tensor(elem: Ty, rank: u32) -> Ty {
    Ty::Tensor(Box::new(elem), rank)
}

fn gate() -> trust_ir::BodyGate {
    trust_ir::BodyGate::Gated {
        authority: "tensor-weight-blobs".into(),
        evidence: None,
    }
}

fn blob(digest: BlobDigest, dims: &[u64]) -> Constant {
    Constant::TensorBlob {
        digest,
        dims: dims.to_vec(),
    }
}

/// `count` deterministic pseudo-random bytes, distinct per `seed`.
fn bytes(seed: u64, count: usize) -> Vec<u8> {
    let mut state = seed
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .wrapping_add(0x2545_f491_4f6c_dd1d);
    (0..count)
        .map(|_| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 56) as u8
        })
        .collect()
}

/// One `fn {name}() -> {ty} { const {ty} {value} }` per case.
fn module_of(name: &str, cases: &[(&str, Ty, Constant)]) -> ModuleBuilder {
    let mut mb = ModuleBuilder::new(name);
    for (fname, ty, value) in cases {
        let ft = mb.add_func_type(vec![], vec![ty.clone()]);
        let mut fb = mb.function(*fname, ft);
        emit_const(&mut fb, ty, value);
        fb.set_body_gate(gate());
        fb.build();
    }
    mb
}

fn emit_const(fb: &mut FunctionBuilder<'_>, ty: &Ty, value: &Constant) {
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let out = fb.const_value(ty.clone(), value.clone());
    fb.ret(vec![out]);
}

fn build(mb: ModuleBuilder) -> Module {
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn target(pointer_size: u32) -> TargetInfo {
    TargetInfo {
        triple: if pointer_size == 4 {
            "wasm32-unknown-unknown".into()
        } else {
            "x86_64-unknown-linux-gnu".into()
        },
        pointer_size,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn func_id(m: &Module, name: &str) -> FuncId {
    m.functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"))
        .id
}

fn run(m: &Module, name: &str) -> InterpretResult<InterpretOutcome> {
    Interpreter::with_module(m).execute_func(func_id(m, name), vec![])
}

/// The returned tensor's extents and its elements' raw bit patterns.
fn computes(m: &Module, name: &str) -> (Vec<u64>, Vec<u128>) {
    let outcome = run(m, name).unwrap_or_else(|e| panic!("{name}: {e:?}"));
    assert_eq!(outcome.steps, 2, "{name}: one fuel unit for the constant");
    let [result] = outcome.returns.as_slice() else {
        panic!("one return, got {:?}", outcome.returns);
    };
    let InterpretValueKind::Tensor { dims, elems } = &result.kind else {
        panic!("{name}: a tensor result, got {result:?}");
    };
    let raws = elems
        .iter()
        .map(|element| element.as_int().expect("integer element").as_unsigned())
        .collect();
    (dims.clone(), raws)
}

/// The interpreter refuses `name` as a `TypeError` whose message holds
/// `needle`.
fn type_error(m: &Module, name: &str, needle: &str) {
    let error = run(m, name).expect_err(name);
    assert_eq!(
        error.code,
        InterpretErrorCode::TypeError,
        "{name}: {error:?}"
    );
    assert!(
        error.message.contains(needle),
        "{name}: {:?} does not say {needle:?}",
        error.message
    );
}

/// The little-endian decode of `data` as `bits`-wide raw patterns: the hand
/// oracle the interpreter's elements are held to.
fn le_raws(data: &[u8], bits: u32) -> Vec<u128> {
    data.chunks_exact((bits / 8) as usize)
        .map(|chunk| {
            chunk
                .iter()
                .rev()
                .fold(0u128, |acc, byte| (acc << 8) | u128::from(*byte))
        })
        .collect()
}

fn reasons(errors: &[ValidationError]) -> Vec<String> {
    errors.iter().map(ToString::to_string).collect()
}

fn blob_table_errors(errors: &[ValidationError]) -> Vec<(usize, &str)> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::InvalidBlobTable { row, reason } => Some((*row, reason.as_str())),
            _ => None,
        })
        .collect()
}

fn tensor_blob_errors(errors: &[ValidationError]) -> Vec<&str> {
    errors
        .iter()
        .filter_map(|e| match e {
            ValidationError::InvalidTensorBlob { reason, .. } => Some(reason.as_str()),
            _ => None,
        })
        .collect()
}

const ELEMENTS: [Ty; 12] = [
    Ty::I8,
    Ty::U8,
    Ty::I16,
    Ty::U16,
    Ty::I32,
    Ty::U32,
    Ty::I64,
    Ty::U64,
    Ty::I128,
    Ty::U128,
    Ty::Isize,
    Ty::Usize,
];

const SHAPES: [&[u64]; 7] = [&[], &[0], &[5], &[2, 3], &[3, 0], &[2, 3, 4], &[1, 1, 7]];

// ───────────────────────────── stored once ─────────────────────────────

#[test]
fn identical_blobs_are_stored_once() {
    let weights = bytes(1, 24);
    let other = bytes(2, 24);
    let mut mb = ModuleBuilder::new("stored_once");
    let first = mb.intern_blob(weights.clone());
    let again = mb.intern_blob(weights.clone());
    let second = mb.intern_blob(other.clone());
    assert_eq!(first, again, "identical bytes intern to one digest");
    assert_eq!(
        first,
        BlobDigest::of(&weights),
        "the digest is plain SHA-256"
    );
    assert_ne!(first, second);
    let ty = tensor(Ty::I32, 2);
    for (name, digest) in [("a", first), ("b", first), ("c", second)] {
        let ft = mb.add_func_type(vec![], vec![ty.clone()]);
        let mut fb = mb.function(name, ft);
        emit_const(&mut fb, &ty, &blob(digest, &[2, 3]));
        fb.set_body_gate(gate());
        fb.build();
    }
    let m = build(mb);
    assert_eq!(m.blobs.len(), 2, "two distinct byte strings, two rows");
    assert!(
        m.blobs.windows(2).all(|w| w[0].digest < w[1].digest),
        "rows land at their canonical ascending position"
    );
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(computes(&m, "a"), computes(&m, "b"));

    // The binary image carries each row's bytes once, though two functions
    // name the first.
    let image = trust_ir::binary::serialize_module(&m).expect("serialize");
    let occurrences = image
        .windows(weights.len())
        .filter(|window| *window == weights.as_slice())
        .count();
    assert_eq!(occurrences, 1, "the shared weight's bytes appear once");
    let back = trust_ir::binary::deserialize_module(&image).expect("deserialize");
    assert_eq!(back.blobs, m.blobs);

    // A merge of two modules that both hold the bytes keeps one row; a row
    // only the source holds joins at its canonical position.
    let mut dst = build(module_of(
        "dst",
        &[("d", ty.clone(), blob(BlobDigest::of(&weights), &[2, 3]))],
    ));
    dst.intern_blob(weights.clone());
    let mut src = build(module_of(
        "src",
        &[
            ("s1", ty.clone(), blob(BlobDigest::of(&weights), &[2, 3])),
            ("s2", ty.clone(), blob(BlobDigest::of(&other), &[3, 2])),
        ],
    ));
    src.intern_blob(weights.clone());
    src.intern_blob(other.clone());
    merge_into(&mut dst, &src, &MergePolicy::EXECUTION_IMAGE).expect("merge");
    assert_eq!(dst.blobs, m.blobs, "the union, each digest once");
    assert_eq!(validate_module(&dst), vec![]);
    let (_, merged) = computes(&dst, "s2");
    assert_eq!(merged, le_raws(&other, 32));
}

#[test]
fn a_merge_refuses_a_source_row_that_does_not_hash_to_its_digest() {
    let mut dst = Module::new("dst");
    let mut src = Module::new("src");
    let digest = src.intern_blob(bytes(3, 8));
    src.blobs[0].data[0] ^= 1;
    let error = merge_into(&mut dst, &src, &MergePolicy::EXECUTION_IMAGE)
        .expect_err("a forged row does not merge");
    assert!(
        error.to_string().contains("do not hash"),
        "{error} names the rule"
    );
    assert!(dst.blobs.is_empty(), "a refused merge leaves dst unchanged");
    assert_eq!(src.blobs[0].digest, digest);
}

// ───────────────────────────── the table's rules ─────────────────────────────

#[test]
fn a_row_whose_bytes_do_not_hash_to_its_digest_is_refused() {
    let weights = bytes(4, 16);
    let mut m = build(module_of(
        "mismatch",
        &[(
            "f",
            tensor(Ty::U8, 1),
            blob(BlobDigest::of(&weights), &[16]),
        )],
    ));
    m.intern_blob(weights);
    assert_eq!(validate_module(&m), vec![]);
    m.blobs[0].data[3] ^= 0x80;
    let errors = validate_module(&m);
    let table = blob_table_errors(&errors);
    assert_eq!(table.len(), 1, "{:?}", reasons(&errors));
    assert_eq!(table[0].0, 0);
    assert!(table[0].1.contains("hash to"), "{}", table[0].1);
    type_error(&m, "f", "do not hash to it");
}

#[test]
fn rows_out_of_order_or_listed_twice_are_refused() {
    let mut m = Module::new("order");
    m.intern_blob(bytes(5, 4));
    m.intern_blob(bytes(6, 4));
    m.intern_blob(bytes(7, 4));
    assert_eq!(validate_module(&m), vec![], "an unused row is admitted");
    let canonical = m.blobs.clone();

    m.blobs.swap(0, 2);
    let errors = validate_module(&m);
    let table = blob_table_errors(&errors);
    assert!(!table.is_empty(), "{:?}", reasons(&errors));
    assert!(
        table
            .iter()
            .all(|(_, reason)| reason.contains("out of canonical order")),
        "{table:?}"
    );

    m.blobs = canonical.clone();
    m.blobs.insert(1, canonical[1].clone());
    let errors = validate_module(&m);
    let table = blob_table_errors(&errors);
    assert_eq!(table.len(), 1, "{:?}", reasons(&errors));
    assert_eq!(table[0].0, 2, "the second listing is the refused row");
    assert!(table[0].1.contains("twice"), "{}", table[0].1);

    // Every decoder refuses the same order (the codec's own rule).
    let image = trust_ir::binary::serialize_module(&m).expect("serialize");
    assert!(trust_ir::binary::deserialize_module(&image).is_err());

    // A row out of order whose bytes also miss its digest is one failing
    // row, reported once, by the order rule.
    m.blobs = canonical.clone();
    let mut tampered = canonical[0].clone();
    tampered.data[0] ^= 1;
    m.blobs.push(tampered);
    let errors = validate_module(&m);
    let table = blob_table_errors(&errors);
    assert_eq!(table.len(), 1, "{:?}", reasons(&errors));
    assert_eq!(table[0].0, 3, "the appended row is the refused row");
    assert!(
        table[0].1.contains("out of canonical order"),
        "{}",
        table[0].1
    );
}

#[test]
fn a_constant_whose_digest_names_no_row_is_refused() {
    let weights = bytes(8, 12);
    let digest = BlobDigest::of(&weights);
    let m = build(module_of(
        "missing",
        &[("f", tensor(Ty::I32, 1), blob(digest, &[3]))],
    ));
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::MissingBlob { digest: named, .. } if *named == digest.to_hex()
        )),
        "{:?}",
        reasons(&errors)
    );
    type_error(&m, "f", "holds no blob");

    // The standalone path has no table; it checks only the constant's shape
    // against its type, and the module pass resolves the digest.
    assert_eq!(validate_function(&m.functions[0]), vec![]);
}

// ───────────────────────────── the constant's rules ─────────────────────────────

#[test]
fn the_constants_rules_are_refused_by_name() {
    let weights = bytes(9, 24);
    let digest = BlobDigest::of(&weights);
    let cases = [
        // C2: two extents for a rank-1 tensor.
        ("rank", tensor(Ty::I32, 1), blob(digest, &[2, 3])),
        // C3: extents whose product reaches 2^64 (at 64-bit pointers no one
        // `u64` extent can reach 2^64; the 32-bit test below refuses one).
        (
            "count",
            tensor(Ty::I8, 2),
            blob(digest, &[1 << 32, 1 << 32]),
        ),
        // C4: 24 bytes are six i32, not five.
        ("length", tensor(Ty::I32, 1), blob(digest, &[5])),
        // C4: 24 bytes are three i64, not two.
        ("width", tensor(Ty::I64, 1), blob(digest, &[2])),
    ];
    let mut m = build(module_of("constant_rules", &cases));
    m.intern_blob(weights);
    let errors = validate_module(&m);
    let refused = tensor_blob_errors(&errors);
    for rule in ["(C2)", "(C3) the extents", "(C4)"] {
        assert!(
            refused.iter().any(|reason| reason.starts_with(rule)),
            "{rule} missing from {refused:?}"
        );
    }
    assert_eq!(refused.len(), cases.len(), "{:?}", reasons(&errors));
    type_error(&m, "rank", "rank 1");
    type_error(&m, "count", "holds 24 bytes");
    type_error(&m, "length", "holds 24 bytes");
    type_error(&m, "width", "holds 24 bytes");
}

#[test]
fn a_32_bit_target_bounds_extents_and_reads_usize_at_four_bytes() {
    let weights = bytes(10, 24);
    let digest = BlobDigest::of(&weights);
    let mut mb = module_of(
        "target32",
        &[
            ("usize", tensor(Ty::Usize, 1), blob(digest, &[6])),
            ("isize", tensor(Ty::Isize, 2), blob(digest, &[3, 2])),
            ("wide", tensor(Ty::U8, 1), blob(digest, &[1 << 32])),
            (
                "product",
                tensor(Ty::U8, 2),
                blob(digest, &[1 << 16, 1 << 16]),
            ),
            ("as64", tensor(Ty::Usize, 1), blob(digest, &[3])),
        ],
    );
    mb.intern_blob(weights.clone());
    let mut m = build(mb);
    m.target_info = Some(target(4));
    let errors = validate_module(&m);
    let refused = tensor_blob_errors(&errors);
    assert_eq!(refused.len(), 3, "{:?}", reasons(&errors));
    assert!(
        refused.iter().any(|r| r.contains("32-bit usize")),
        "{refused:?}"
    );
    assert!(refused.iter().any(|r| r.contains("2^32")), "{refused:?}");
    assert!(refused.iter().any(|r| r.starts_with("(C4)")), "{refused:?}");
    assert_eq!(computes(&m, "usize"), (vec![6], le_raws(&weights, 32)));
    assert_eq!(computes(&m, "isize"), (vec![3, 2], le_raws(&weights, 32)));
    type_error(&m, "wide", "32-bit usize");
    type_error(&m, "product", "holds 24 bytes");
    type_error(&m, "as64", "holds 24 bytes");

    // The same shapes at the 64-bit width: usize is eight bytes.
    m.target_info = Some(target(8));
    assert_eq!(computes(&m, "as64"), (vec![3], le_raws(&weights, 64)));
    type_error(&m, "usize", "holds 24 bytes");
}

#[test]
fn a_blob_stands_only_as_the_whole_value_of_a_const() {
    let weights = bytes(11, 4);
    let digest = BlobDigest::of(&weights);
    let ty = tensor(Ty::U8, 1);

    // C1: nested as a lane of a tuple constant.
    let mut mb = ModuleBuilder::new("placement");
    mb.intern_blob(weights.clone());
    let lane = Ty::Tuple(vec![ty.clone(), Ty::U8]);
    let ft = mb.add_func_type(vec![], vec![lane.clone()]);
    let mut fb = mb.function("nested", ft);
    emit_const(
        &mut fb,
        &lane,
        &Constant::Aggregate(vec![blob(digest, &[4]), Constant::Int(0)]),
    );
    fb.set_body_gate(gate());
    fb.build();
    // C1: the payload of an enum constant. A payload lane adds no path
    // element to the walk, so placement reads the walk's root, never the
    // path.
    let wrapped = mb.add_enum(EnumDef {
        id: EnumId::new(0),
        name: "Wrapped".into(),
        variants: vec![EnumVariant {
            name: "Weights".into(),
            fields: vec![ty.clone()],
            field_names: Vec::new(),
        }],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
        origin: None,
    });
    let payload = Ty::Enum(wrapped);
    let ft = mb.add_func_type(vec![], vec![payload.clone()]);
    let mut fb = mb.function("payload", ft);
    emit_const(
        &mut fb,
        &payload,
        &Constant::Aggregate(vec![Constant::Int(0), blob(digest, &[4])]),
    );
    fb.set_body_gate(gate());
    fb.build();
    // C1: a closure capture, which adds no path element either.
    let code = mb.add_func_type(vec![ty.clone()], vec![Ty::U8]);
    let mut fb = mb.function("code", code);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let zero = fb.const_value(Ty::U8, Constant::Int(0));
    fb.ret(vec![zero]);
    fb.set_body_gate(gate());
    let code_id = fb.build();
    let bare = mb.add_func_type(vec![], vec![Ty::U8]);
    let closure = Ty::Closure(mb.add_closure_type(ClosureTy {
        func: bare,
        captures: vec![ty.clone()],
    }));
    let ft = mb.add_func_type(vec![], vec![closure.clone()]);
    let mut fb = mb.function("capture", ft);
    emit_const(
        &mut fb,
        &closure,
        &Constant::Closure {
            func: code_id,
            captures: vec![blob(digest, &[4])],
        },
    );
    fb.set_body_gate(gate());
    fb.build();
    // C1: a global initializer.
    mb.add_global(Global {
        name: "weights".into(),
        ty: ty.clone(),
        initializer: Some(blob(digest, &[4])),
        mutable: false,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    });
    let m = build(mb);
    let errors = validate_module(&m);
    let refused = tensor_blob_errors(&errors);
    assert_eq!(refused.len(), 4, "{:?}", reasons(&errors));
    assert!(
        refused.iter().all(|reason| reason.starts_with("(C1)")),
        "{refused:?}"
    );
    assert_eq!(
        refused
            .iter()
            .filter(|r| r.contains("a global initializer"))
            .count(),
        1
    );
    assert_eq!(
        refused
            .iter()
            .filter(|r| r.contains("nested in an aggregate"))
            .count(),
        3
    );
    // The interpreter gives none of them a meaning at run time either (SemR
    // is held to the same refusal in `lean_exec_differential`).
    for name in ["nested", "payload", "capture"] {
        type_error(&m, name, "misplaced tensor blob constant");
    }
}

#[test]
fn a_float_element_is_refused_by_its_type() {
    let weights = bytes(12, 16);
    let digest = BlobDigest::of(&weights);
    let mut mb = module_of("float", &[("f", tensor(Ty::F32, 1), blob(digest, &[4]))]);
    mb.intern_blob(weights);
    let m = build(mb);
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidTensorType { .. })),
        "{:?}",
        reasons(&errors)
    );
    assert!(
        tensor_blob_errors(&errors).is_empty(),
        "the element is the type's refusal, not the constant's: {:?}",
        reasons(&errors)
    );
    type_error(&m, "f", "no integer shape");
}

#[test]
fn a_blob_at_a_type_that_is_not_a_tensor_is_a_shape_mismatch() {
    let weights = bytes(13, 4);
    let mut mb = module_of(
        "shape",
        &[("f", Ty::U32, blob(BlobDigest::of(&weights), &[]))],
    );
    mb.intern_blob(weights);
    let m = build(mb);
    let errors = validate_module(&m);
    assert!(
        errors
            .iter()
            .any(|e| matches!(e, ValidationError::ConstTypeMismatch { .. })),
        "{:?}",
        reasons(&errors)
    );
}

// ───────────────────────────── the interpreter ─────────────────────────────

#[test]
fn every_integer_element_and_shape_reads_its_bytes_little_endian() {
    let mut mb = ModuleBuilder::new("elements");
    let mut expected = Vec::new();
    for (e, elem) in ELEMENTS.iter().enumerate() {
        let bits = elem.bit_width_with(64).expect("integer width");
        for (s, dims) in SHAPES.iter().enumerate() {
            let count: u64 = dims.iter().product();
            let data = bytes((e * 100 + s) as u64, (count * u64::from(bits / 8)) as usize);
            let digest = mb.intern_blob(data.clone());
            let name = format!("f_{e}_{s}");
            let ty = tensor(elem.clone(), dims.len() as u32);
            let ft = mb.add_func_type(vec![], vec![ty.clone()]);
            let mut fb = mb.function(&name, ft);
            emit_const(&mut fb, &ty, &blob(digest, dims));
            fb.set_body_gate(gate());
            fb.build();
            expected.push((name, dims.to_vec(), le_raws(&data, bits)));
        }
    }
    let m = build(mb);
    assert_eq!(validate_module(&m), vec![]);
    assert_eq!(
        validate_module_for_codegen(&m)
            .iter()
            .filter(|e| matches!(
                e,
                ValidationError::UnlowerableForCodegen { inst: "Const", .. }
            ))
            .count(),
        expected.len(),
        "the codegen gate refuses each blob constant by name"
    );
    let empty = BlobDigest::of(&[]);
    assert!(
        m.blob(&empty).is_some(),
        "the zero-element tensors share one empty row"
    );
    for (name, dims, raws) in expected {
        assert_eq!(computes(&m, &name), (dims, raws), "{name}");
    }
    // A signed element keeps its sign: 0xff at i8 is -1.
    let mut mb = ModuleBuilder::new("sign");
    let digest = mb.intern_blob(vec![0xff, 0x7f, 0x80, 0x00]);
    let ty = tensor(Ty::I8, 1);
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut fb = mb.function("f", ft);
    emit_const(&mut fb, &ty, &blob(digest, &[4]));
    fb.set_body_gate(gate());
    fb.build();
    let m = build(mb);
    let outcome = run(&m, "f").expect("runs");
    let InterpretValueKind::Tensor { elems, .. } = &outcome.returns[0].kind else {
        panic!("a tensor");
    };
    let signed: Vec<i128> = elems
        .iter()
        .map(|e| e.as_int().expect("int").as_signed())
        .collect();
    assert_eq!(signed, vec![-1, 127, -128, 0]);
}

// ───────────────────────────── the body digest ─────────────────────────────

#[test]
fn a_body_digest_reads_the_digest_never_the_bytes() {
    let weights = bytes(14, 32);
    let digest = BlobDigest::of(&weights);
    let mut mb = module_of(
        "body_digest",
        &[("f", tensor(Ty::U64, 1), blob(digest, &[4]))],
    );
    mb.intern_blob(weights.clone());
    let m = build(mb);
    let f = func_id(&m, "f");
    let body = m.function_body_digest(f).expect("body digest");
    let stable = m.stable_digest();

    // Only the row's bytes change (the row then fails B2, which is the
    // validator's question, not the body's identity).
    let mut replaced = m.clone();
    replaced.blobs[0].data = bytes(15, 32);
    assert_eq!(replaced.function_body_digest(f).expect("body"), body);
    assert_ne!(
        replaced.stable_digest(),
        stable,
        "the module's identity moves"
    );

    // A row the body does not name joins, then the named row leaves.
    let mut added = m.clone();
    added.intern_blob(bytes(16, 7));
    assert_eq!(added.function_body_digest(f).expect("body"), body);
    assert_ne!(added.stable_digest(), stable);
    let mut dropped = m.clone();
    dropped.blobs.clear();
    assert_eq!(dropped.function_body_digest(f).expect("body"), body);
    assert_ne!(dropped.stable_digest(), stable);

    // A body that names other bytes names another digest, and is another
    // body.
    let other = bytes(17, 32);
    let mut renamed = module_of(
        "body_digest",
        &[("f", tensor(Ty::U64, 1), blob(BlobDigest::of(&other), &[4]))],
    );
    renamed.intern_blob(other);
    let renamed = build(renamed);
    assert_ne!(renamed.function_body_digest(f).expect("body"), body);
    // So do other extents over the same bytes.
    let reshaped = build(module_of(
        "body_digest",
        &[("f", tensor(Ty::U64, 2), blob(digest, &[2, 2]))],
    ));
    assert_ne!(reshaped.function_body_digest(f).expect("body"), body);
}

#[test]
fn a_blob_table_round_trips_through_every_codec() {
    let weights = bytes(18, 6);
    let mut mb = module_of(
        "codecs",
        &[(
            "f",
            tensor(Ty::I16, 2),
            blob(BlobDigest::of(&weights), &[1, 3]),
        )],
    );
    mb.intern_blob(weights);
    mb.intern_blob(Vec::new());
    let m = build(mb);
    let image = trust_ir::binary::serialize_module(&m).expect("serialize");
    assert_eq!(
        trust_ir::binary::deserialize_module(&image).expect("binary"),
        m
    );
    let text = m.to_string();
    assert!(text.contains("tensor_blob<"), "{text}");
    let parsed = trust_ir::parser::parse_module(&text).expect("parse");
    assert_eq!(parsed.blobs, m.blobs);
    assert_eq!(
        trust_ir::binary::serialize_module(&parsed).expect("serialize"),
        image,
        "text carries the table and the constant losslessly"
    );
    for row in &m.blobs {
        assert_eq!(*row, Blob::new(row.data.clone()));
    }
}
