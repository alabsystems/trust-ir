// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// The level-S must-refuse corpus (amendment S, §8;
// `tests/fixtures/refuse_templates/MANIFEST.tsv`): every row byte-pinned
// against its builder, every pinned verdict run against the entry point that
// returns it on the CHECKED-IN artifact, and every variant of the three
// level-S refusal enums exhibited by a row (`TemplateError`,
// `TemplateViolation`, `InstantiateError`: no allowlist, S11). The `control`
// row must be accepted, so a refuse-everything consumer cannot pass.
//
// Regenerate the artifacts with `TRUST_IR_UPDATE_FIXTURES=1`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use trust_ir::template::{ScriptedHost, Template, TemplateError};
use trust_ir_build::template::{
    InstantiateError, TemplateViolation, instantiate, validate_template,
};
use trust_ir_conformance::refuse_template_fixtures::{Artifact, artifacts};

fn dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("refuse_templates")
}

fn update_mode() -> bool {
    std::env::var_os("TRUST_IR_UPDATE_FIXTURES").is_some()
}

#[derive(Debug)]
struct Row {
    id: String,
    carrier: String,
    verdicts: Vec<(String, String)>,
}

fn manifest() -> Vec<Row> {
    let text = std::fs::read_to_string(dir().join("MANIFEST.tsv")).expect("the manifest");
    let mut rows = Vec::new();
    let mut header = false;
    for line in text.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let cells: Vec<&str> = line.split('\t').collect();
        if !header {
            assert_eq!(cells, ["row", "carrier", "verdicts", "obligation", "why"]);
            header = true;
            continue;
        }
        assert_eq!(cells.len(), 5, "five tab-separated cells: {line}");
        assert!(
            ["template_bytes", "template", "instance", "control"].contains(&cells[1]),
            "carrier `{}`",
            cells[1]
        );
        let verdicts = cells[2]
            .split(';')
            .map(|pair| {
                let (entry, verdict) = pair.split_once('=').expect("entry=verdict");
                (entry.to_string(), verdict.to_string())
            })
            .collect();
        rows.push(Row {
            id: cells[0].to_string(),
            carrier: cells[1].to_string(),
            verdicts,
        });
    }
    assert!(!rows.is_empty(), "the template corpus cannot be vacuous");
    rows
}

fn files_of(id: &str, artifact: &Artifact) -> Vec<(PathBuf, Vec<u8>)> {
    match artifact {
        Artifact::Bytes(bytes) => vec![(dir().join(format!("{id}.tmbs")), bytes.clone())],
        Artifact::Template(template, host) => {
            let mut files = vec![(
                dir().join(format!("{id}.json")),
                serde_json::to_string_pretty(template)
                    .expect("a template serializes")
                    .into_bytes(),
            )];
            if let Some(host) = host {
                files.push((
                    dir().join(format!("{id}.host.json")),
                    serde_json::to_string_pretty(host)
                        .expect("a host script serializes")
                        .into_bytes(),
                ));
            }
            files
        }
    }
}

#[test]
fn goldens_pin_every_row_and_the_directory_is_exact() {
    let rows = manifest();
    let built: BTreeMap<&str, Artifact> = artifacts()
        .expect("every refuse-template row builds")
        .into_iter()
        .collect();
    let ids: BTreeSet<&str> = rows.iter().map(|row| row.id.as_str()).collect();
    assert_eq!(
        ids,
        built.keys().copied().collect::<BTreeSet<_>>(),
        "every manifest row has a builder and every builder a row"
    );
    let mut expected_files = BTreeSet::new();
    expected_files.insert(dir().join("MANIFEST.tsv"));
    for (id, artifact) in &built {
        for (path, bytes) in files_of(id, artifact) {
            if update_mode() {
                std::fs::write(&path, &bytes).expect("write golden");
            } else {
                let golden = std::fs::read(&path).unwrap_or_else(|e| {
                    panic!(
                        "missing {} ({e}); TRUST_IR_UPDATE_FIXTURES=1",
                        path.display()
                    )
                });
                assert_eq!(golden, bytes, "{} drifted from its builder", path.display());
            }
            expected_files.insert(path);
        }
    }
    let on_disk: BTreeSet<PathBuf> = std::fs::read_dir(dir())
        .expect("the template corpus directory")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    assert_eq!(on_disk, expected_files, "no orphan and no missing artifact");
}

fn read_template(id: &str) -> Template {
    let text = std::fs::read_to_string(dir().join(format!("{id}.json"))).expect("row json");
    serde_json::from_str(&text).expect("a template decodes")
}

fn read_host(id: &str) -> ScriptedHost {
    let text = std::fs::read_to_string(dir().join(format!("{id}.host.json"))).expect("host json");
    serde_json::from_str(&text).expect("a host script decodes")
}

fn variant(value: &impl std::fmt::Debug) -> String {
    format!("{value:?}")
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect()
}

/// What an entry point returns for a row, as `<Class>:<Variant>` or `accepts`.
fn measure(entry: &str, row: &Row) -> String {
    match entry {
        "deserialize_template" => {
            let bytes = std::fs::read(dir().join(format!("{}.tmbs", row.id))).expect("row blob");
            match trust_ir::binary::deserialize_template(&bytes) {
                Ok(_) => "accepts".into(),
                Err(error) => format!("Template:{}", variant(&error)),
            }
        }
        "validate_template" => match validate_template(&read_template(&row.id)).first() {
            None => "accepts".into(),
            Some(TemplateViolation::Structure(error)) => format!("Template:{}", variant(error)),
            Some(TemplateViolation::LevelR(error)) => format!("LevelR:{}", variant(error)),
        },
        "instantiate" => {
            let mut host = read_host(&row.id);
            match instantiate(&read_template(&row.id), &mut host) {
                Ok(_) => "accepts".into(),
                Err(error) => format!("Instantiate:{}", variant(&error)),
            }
        }
        other => panic!("unknown entry point `{other}`"),
    }
}

#[test]
fn every_pinned_verdict_holds_on_the_checked_in_artifact() {
    for row in manifest() {
        for (entry, verdict) in &row.verdicts {
            assert_eq!(&measure(entry, &row), verdict, "{} at {entry}", row.id);
        }
        if row.carrier == "control" {
            assert!(
                row.verdicts.iter().all(|(_, v)| v == "accepts"),
                "{}: a control row is accepted",
                row.id
            );
        }
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
            let name: String = trimmed
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            out.push(name);
        }
        depth += line.matches(['{', '(']).count() as i32;
        depth -= line.matches(['}', ')']).count() as i32;
        if depth < 0 {
            break;
        }
    }
    out
}

#[test]
fn every_level_s_refusal_variant_is_exhibited_by_a_row() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let template_rs = std::fs::read_to_string(root.join("trust-ir/src/template.rs")).unwrap();
    let build_rs = std::fs::read_to_string(root.join("trust-ir-build/src/template.rs")).unwrap();
    let rows = manifest();
    let named: BTreeSet<String> = rows
        .iter()
        .flat_map(|row| row.verdicts.iter().map(|(_, v)| v.clone()))
        .collect();
    let mut missing = Vec::new();
    for v in enum_variants(&template_rs, "TemplateError") {
        if !named.contains(&format!("Template:{v}")) {
            missing.push(format!("TemplateError::{v}"));
        }
    }
    for v in enum_variants(&build_rs, "InstantiateError") {
        if !named.contains(&format!("Instantiate:{v}")) {
            missing.push(format!("InstantiateError::{v}"));
        }
    }
    let violations = enum_variants(&build_rs, "TemplateViolation");
    assert_eq!(violations, ["Structure", "LevelR"]);
    if !named.iter().any(|v| v.starts_with("LevelR:")) {
        missing.push("TemplateViolation::LevelR".into());
    }
    if !rows.iter().any(|row| {
        row.verdicts
            .iter()
            .any(|(entry, v)| entry == "validate_template" && v.starts_with("Template:"))
    }) {
        missing.push("TemplateViolation::Structure".into());
    }
    assert!(missing.is_empty(), "variants no row exhibits: {missing:?}");
    // The census is not vacuous: it read every enum.
    assert!(enum_variants(&template_rs, "TemplateError").len() >= 19);
    assert!(enum_variants(&build_rs, "InstantiateError").len() >= 9);
    let _ = (
        TemplateError::NotATemplate,
        InstantiateError::ArityMismatch {
            expected: 0,
            got: 0,
        },
    );
}
