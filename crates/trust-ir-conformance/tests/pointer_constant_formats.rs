// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3.8 / F-049: non-null pointer constants cross every format unchanged.
//
// The admission of `SymbolAddr` at `Ref`/`PtrConst`/`PtrMut` and of
// `[SymbolAddr, Int]` at `fatptr<str>` / `fatptr<[T]>` is a VALIDATOR rule
// over constructors that already exist (`Constant::SymbolAddr`,
// `Constant::Aggregate`), so it has no wire impact: such a module still writes
// the legacy v38 header, and binary / JSON / MessagePack round-trip it
// losslessly while canonical text is idempotent and re-validates. The
// validator's accept/refuse matrix lives in
// `trust-ir-build/tests/pointer_constants.rs`.

use trust_ir::ty::{EnumDef, EnumVariant};
use trust_ir::{Constant, EnumId, FatPtrKind, Global, Linkage, Module, Ty, Visibility};
use trust_ir_build::{ModuleBuilder, validate_module};

fn global(name: &str, ty: Ty, initializer: Constant) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable: false,
        initializer: Some(initializer),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn fat(symbol: &str, addend: i64, len: i128) -> Constant {
    Constant::Aggregate(vec![
        Constant::symbol_addr_with_addend(symbol, addend),
        Constant::Int(len),
    ])
}

/// `const E: Option<&'static str> = Some("x")` in a body, a `[&str; 2]`
/// table, a `&[u32]` window and a `&'static u64` — every WS3.8 spelling.
fn module() -> Module {
    let str_ty = Ty::FatPtr(FatPtrKind::Str);
    let mut mb = ModuleBuilder::new("ws3_8_formats");
    let u8_id = mb.add_type(Ty::U8);
    let u32_id = mb.add_type(Ty::U32);
    let str_id = mb.add_type(str_ty.clone());
    mb.add_global(global("X", Ty::Array(u8_id, 2), Constant::str_bytes("xy")));
    mb.add_global(global(
        "NAMES",
        Ty::Array(str_id, 2),
        Constant::Array(vec![fat("X", 0, 1), fat("X", 1, 1)]),
    ));
    mb.add_global(global(
        "TABLE",
        Ty::Array(u32_id, 3),
        Constant::Array(vec![Constant::Int(1), Constant::Int(2), Constant::Int(3)]),
    ));
    mb.add_global(global(
        "VIEW",
        Ty::FatPtr(FatPtrKind::Slice(u32_id)),
        fat("TABLE", 4, 2),
    ));
    mb.add_global(global("ANSWER", Ty::U64, Constant::Int(42)));
    mb.add_global(global(
        "ANSWER_REF",
        Ty::Ref(Box::new(Ty::U64)),
        Constant::symbol_addr("ANSWER"),
    ));
    let option = mb.add_enum(EnumDef::new(
        EnumId::new(0),
        "Option",
        vec![
            EnumVariant {
                name: "None".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Some".into(),
                fields: vec![str_ty],
                field_names: vec![],
            },
        ],
    ));
    let ft = mb.add_func_type(vec![], vec![Ty::Enum(option)]);
    let mut f = mb.function("e", ft);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let v = f.const_value(
        Ty::Enum(option),
        Constant::Aggregate(vec![Constant::Int(1), fat("X", 0, 1)]),
    );
    f.ret(vec![v]);
    f.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn pointer_constant_formats() {
    let m = module();
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "{errors:?}");

    // Binary: no wire change — the legacy v38 header, lossless, idempotent.
    let b1 = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let version = u32::from_le_bytes(b1[8..12].try_into().expect("header"));
    assert_eq!(
        version, 38,
        "WS3.8 is a validator rule; it must not select a newer wire version"
    );
    let m2 = trust_ir::binary::deserialize_module(&b1).expect("binary decode");
    assert_eq!(m, m2, "binary round-trip changed the module");
    assert_eq!(
        b1,
        trust_ir::binary::serialize_module(&m2).expect("serialize_module: test fixture")
    );

    // serde JSON and MessagePack: lossless.
    let json = serde_json::to_string(&m).expect("json");
    assert_eq!(
        m,
        serde_json::from_str::<Module>(&json).expect("json decode")
    );
    let mp = rmp_serde::to_vec(&m).expect("msgpack");
    assert_eq!(
        m,
        rmp_serde::from_slice::<Module>(&mp).expect("msgpack decode")
    );

    // Canonical text: idempotent, and the re-parsed module still validates.
    let t1 = trust_ir::format::canonical(&m);
    let mt = trust_ir::parser::parse_module(&t1).expect("text parse");
    assert_eq!(t1, trust_ir::format::canonical(&mt));
    let reparsed = validate_module(&mt);
    assert!(reparsed.is_empty(), "{reparsed:?}\n{t1}");
}
