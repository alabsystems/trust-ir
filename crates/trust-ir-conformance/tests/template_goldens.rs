// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// The level-S golden templates (amendment S, §8):
// `tests/fixtures/templates/<name>.{tmbs,trust_irs,json,msgpack}`, one per
// feature, byte-pinned in four formats against its builder
// (`tests/generate/templates.rs`), each format decoding back to the builder's
// template, and every variant of the five level-S carrier enums exercised by
// some golden (read from the source: no allowlist).
//
// Regenerate with `TRUST_IR_UPDATE_FIXTURES=1`, selecting only
// `template_goldens_round_trip_in_four_formats_and_the_directory_is_exact`.
// Then run this whole target normally: its readers require generation to finish.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use trust_ir::template::{
    HoleKind, RefCollector, Template, TemplateArg, TemplateParam, TypeContract,
};
use trust_ir::{ConstantG, InstG, TemplateRef};
use trust_ir_conformance::template_fixtures::corpus;

fn dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("templates")
}

fn update_mode() -> bool {
    std::env::var_os("TRUST_IR_UPDATE_FIXTURES").is_some()
}

fn pin(path: &Path, got: &[u8]) {
    if update_mode() {
        std::fs::write(path, got).expect("write golden");
        return;
    }
    let golden = std::fs::read(path).unwrap_or_else(|e| {
        panic!(
            "missing {} ({e}); regenerate with TRUST_IR_UPDATE_FIXTURES=1",
            path.display()
        )
    });
    assert_eq!(golden, got, "{} drifted from its builder", path.display());
}

#[test]
fn template_goldens_round_trip_in_four_formats_and_the_directory_is_exact() {
    let mut expected = BTreeSet::new();
    for (name, template) in corpus().expect("template fixture") {
        // Binary: the TRUST_IS blob.
        let bytes = trust_ir::binary::serialize_template(&template)
            .unwrap_or_else(|e| panic!("{name} encodes: {e}"));
        assert_eq!(
            trust_ir::binary::deserialize_template(&bytes).expect("decodes"),
            template,
            "{name}: binary round trip"
        );
        // Text.
        let text = template.to_string();
        assert_eq!(
            trust_ir::parser::parse_template(&text)
                .unwrap_or_else(|e| panic!("{name} parses: {e}\n{text}")),
            template,
            "{name}: text round trip"
        );
        // JSON.
        let json = serde_json::to_string_pretty(&template).expect("json");
        assert_eq!(
            serde_json::from_str::<Template>(&json).expect("json decodes"),
            template,
            "{name}: json round trip"
        );
        // MessagePack.
        let msgpack = rmp_serde::to_vec(&template).expect("msgpack");
        assert_eq!(
            rmp_serde::from_slice::<Template>(&msgpack).expect("msgpack decodes"),
            template,
            "{name}: msgpack round trip"
        );
        for (extension, got) in [
            ("tmbs", bytes),
            ("trust_irs", text.into_bytes()),
            ("json", json.into_bytes()),
            ("msgpack", msgpack),
        ] {
            let path = dir().join(format!("{name}.{extension}"));
            pin(&path, &got);
            expected.insert(path);
        }
    }
    let on_disk: BTreeSet<PathBuf> = std::fs::read_dir(dir())
        .expect("the template golden directory")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    assert_eq!(on_disk, expected, "no orphan and no missing golden");
}

#[test]
fn checked_in_template_goldens_decode_to_their_builders() {
    // The pins above compare bytes; this decodes the CHECKED-IN files, so a
    // reader change that still writes the same bytes but reads them wrongly
    // fails here.
    for (name, template) in corpus().expect("template fixture") {
        let blob = std::fs::read(dir().join(format!("{name}.tmbs"))).expect("blob");
        assert_eq!(
            trust_ir::binary::deserialize_template(&blob).expect("the golden decodes"),
            template,
            "{name}.tmbs"
        );
        let text = std::fs::read_to_string(dir().join(format!("{name}.trust_irs"))).expect("text");
        assert_eq!(
            trust_ir::parser::parse_template(&text).expect("the golden parses"),
            template,
            "{name}.trust_irs"
        );
        assert_eq!(
            template.check_structure(),
            Ok(()),
            "{name} is structurally valid"
        );
    }
}

fn enum_variants(source: &str, name: &str) -> Vec<String> {
    let header = format!("pub enum {name} {{");
    let start = source
        .find(&header)
        .unwrap_or_else(|| panic!("{header} not found"));
    let mut out = Vec::new();
    let mut depth = 0i32;
    for line in source[start + header.len()..].lines() {
        let trimmed = line.trim_start();
        if depth == 0
            && trimmed.starts_with(|c: char| c.is_ascii_uppercase())
            && !trimmed.starts_with("//")
        {
            out.push(
                trimmed
                    .chars()
                    .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                    .collect(),
            );
        }
        depth += line.matches(['{', '(']).count() as i32;
        depth -= line.matches(['}', ')']).count() as i32;
        if depth < 0 {
            break;
        }
    }
    out
}

fn refs_of(template: &Template) -> BTreeSet<TemplateRef> {
    let module = &template.module;
    let mut refs = RefCollector::new(module);
    let mut out = BTreeSet::new();
    for ty in &module.types {
        refs.ty(ty, &mut out);
    }
    for signature in &module.func_types {
        for ty in signature.params.iter().chain(&signature.returns) {
            refs.ty(ty, &mut out);
        }
    }
    for function in &module.functions {
        for block in &function.blocks {
            for (_, ty) in &block.params {
                refs.ty(ty, &mut out);
            }
            for node in &block.body {
                let mut tys = Vec::new();
                node.inst.for_each_ty(|ty| tys.push(ty));
                for ty in tys {
                    refs.ty(ty, &mut out);
                }
                if let InstG::Const {
                    value: ConstantG::Ext(r),
                    ..
                } = &node.inst
                {
                    out.insert(*r);
                }
            }
        }
    }
    out
}

#[test]
fn every_level_s_carrier_variant_is_exercised_by_a_golden() {
    let mut seen: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
    let mut mark = |space: &'static str, variant: &str| {
        seen.entry(space).or_default().insert(variant.to_string());
    };
    for (_, template) in corpus().expect("template fixture") {
        for r in refs_of(&template) {
            mark(
                "TemplateRef",
                match r {
                    TemplateRef::Param(_) => "Param",
                    TemplateRef::Hole(_) => "Hole",
                },
            );
        }
        for p in &template.header.params {
            mark(
                "TemplateParam",
                match p {
                    TemplateParam::Type => "Type",
                    TemplateParam::Const { .. } => "Const",
                    TemplateParam::Host => "Host",
                },
            );
        }
        for hole in &template.header.holes {
            match &hole.kind {
                HoleKind::Type { contract } => {
                    mark("HoleKind", "Type");
                    mark(
                        "TypeContract",
                        match contract {
                            TypeContract::Opaque => "Opaque",
                            TypeContract::ThinPointer => "ThinPointer",
                            TypeContract::Struct { .. } => "Struct",
                            TypeContract::Enum { .. } => "Enum",
                        },
                    );
                }
                HoleKind::Const { .. } => mark("HoleKind", "Const"),
                HoleKind::Callee { .. } => mark("HoleKind", "Callee"),
                HoleKind::Global { .. } => mark("HoleKind", "Global"),
            }
            for arg in &hole.args {
                mark(
                    "TemplateArg",
                    match arg {
                        TemplateArg::Type(_) => "Type",
                        TemplateArg::Const { .. } => "Const",
                        TemplateArg::Host(_) => "Host",
                    },
                );
            }
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-ir/src");
    let level = std::fs::read_to_string(root.join("level.rs")).expect("level.rs");
    let template = std::fs::read_to_string(root.join("template.rs")).expect("template.rs");
    for (space, source) in [
        ("TemplateRef", &level),
        ("TemplateParam", &template),
        ("HoleKind", &template),
        ("TypeContract", &template),
        ("TemplateArg", &template),
    ] {
        let declared: BTreeSet<String> = enum_variants(source, space).into_iter().collect();
        assert!(declared.len() >= 2, "{space}: the scan read the enum");
        let exercised = seen.get(space).cloned().unwrap_or_default();
        let missing: Vec<_> = declared.difference(&exercised).collect();
        assert!(
            missing.is_empty(),
            "{space} variants no golden exercises: {missing:?}"
        );
    }
}
