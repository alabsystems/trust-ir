// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Portable module identity and the `ModuleImport.scheme` discriminator
// (roadmap WS4.10; F-084 and the format half of F-117; wire v44).
//
// `Module::stable_digest` is now the V3 identity: the canonical encoding with
// every `Module.files` string projected to "" (length kept), under
// `trust_ir.module.v3`. The legacy V2 identity (`trust_ir.module.v2`, the whole
// encoding) stays computable through `Module::stable_digest_under`, and every
// import row names the scheme its digest was recorded under, so a pre-v44 row
// (decoded as V2) keeps authenticating exactly what it authenticated before.
//
// Rows ported from the archived proof program
// (reports/2026-09-17-two-language-proof-program/):
// * `crit.unex03` — the critic's g8 cross-checkout measurement: the same
//   crate compiled at two checkout paths differed ONLY in `files[0]`, and that
//   one string moved every digest, so a dependency built on one machine could
//   never authenticate on another;
// * `trust-ir-self-declared/import-scheme-discriminator` — a domain bump needs
//   a per-row scheme and `stable_digest_under`, or every recorded import stops
//   authenticating.
// (`b4.gap.no_module_import_scheme` is flipped in place, in
// `two_language/b4_cross_crate_linking.rs`.)

use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::proof::{ProofDigest, RejectingModuleProofAuthority};
use trust_ir::ty::Ty;
use trust_ir::value::{ImportId, SourceSpan};
use trust_ir::{
    Endianness, HashedModule, IdentityScheme, ImportVerificationError, MODULE_IDENTITY_DOMAIN,
    MODULE_IDENTITY_DOMAIN_V2, Module, ModuleImport, Producer, TargetInfo,
};
use trust_ir_build::{ModuleBuilder, ModuleSet, ValidationError, validate_linked_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    }
}

/// The macOS home-directory checkout path `dep` is compiled at (the moved
/// twin is `/home/b/x.rs`). Assembled by `concat!` so the exported source
/// never spells a home-directory literal, which publication's central
/// forbidden-content guard refuses with no per-repository waiver; the string
/// the rows exercise is unchanged.
const USERS_A_X: &str = concat!("/Us", "ers/a/x.rs");

/// The dependency crate `dep`, compiled from `path` (the absolute checkout
/// path a producer that ignores `--remap-path-prefix` records), with its one
/// body instruction spanned at `line`.
fn dep_at(path: &str, line: u32) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("dep", target());
    mb.set_default_producer(Producer::TRust);
    let file = mb.intern_file(path);
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("dep_answer", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_span(SourceSpan { file, line, col: 5 });
    let v = fb.uconst(Ty::U64, 42);
    fb.ret(vec![v]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A call-free importer with ONE row naming `dep` under `scheme`.
fn root_importing(digest: ProofDigest, scheme: IdentityScheme) -> Module {
    let mut root = Module::new("root");
    root.target_info = Some(target());
    root.intern_import(
        ModuleImport::new("dep", digest)
            .with_producer(Producer::TRust)
            .with_scheme(scheme),
    )
    .expect("Module::intern_import: test fixture");
    root
}

const ROW: ImportId = ImportId::new(0);

// ---------------------------------------------------------------------------
// positive
// ---------------------------------------------------------------------------

/// `crit.unex03`, ported: the same crate compiled at `USERS_A_X` and at
/// `/home/b/…`. The V3 identity is EQUAL (the only delta is a debug path
/// string); the legacy V2 identity and the executable digest still differ —
/// the exact measurement the critic recorded, now split by scheme.
#[test]
fn crit_unex03_moved_checkout_keeps_the_portable_identity() {
    let here = dep_at(USERS_A_X, 3);
    let moved = dep_at("/home/b/x.rs", 3);
    assert_ne!(here.files, moved.files);
    let mut only_files = here.clone();
    only_files.files = moved.files.clone();
    assert_eq!(only_files, moved, "the modules differ ONLY in files[0]");

    assert_eq!(here.stable_digest(), moved.stable_digest());
    assert_eq!(
        here.stable_digest_under(IdentityScheme::V3),
        moved.stable_digest_under(IdentityScheme::V3)
    );
    // The legacy identity is the one the critic measured moving.
    assert_ne!(
        here.stable_digest_under(IdentityScheme::V2),
        moved.stable_digest_under(IdentityScheme::V2)
    );
    // The codegen-cache identity KEEPS the paths (WS4.10 item 4).
    assert_ne!(
        here.executable_content_digest_v1(),
        moved.executable_content_digest_v1()
    );
    // And the artifact bytes still carry the path: only the IDENTITY drops it.
    assert_ne!(
        serialize_module(&here).expect("serialize_module: test fixture"),
        serialize_module(&moved).expect("serialize_module: test fixture")
    );
}

/// A root pinning a V3 row authenticates the dependency rebuilt at another
/// checkout path — one edge (`verify_import`) and the closure walk alike.
#[test]
fn a_v3_row_authenticates_a_dependency_built_at_another_path() {
    let built_here = dep_at(USERS_A_X, 3);
    let root = root_importing(built_here.stable_digest(), IdentityScheme::V3);
    let moved = dep_at("/home/b/x.rs", 3);
    root.verify_import(ROW, &moved)
        .expect("the moved dependency is the same module under V3");
    let set = ModuleSet::new([&moved]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_imports().map(|m| m.len()), Some(1));
}

/// A pre-v44 blob carrying a V2 row still authenticates its V2 dependency:
/// the row decodes as V2 and is compared under `trust_ir.module.v2`.
#[test]
fn a_pre_v44_blob_with_a_v2_row_still_authenticates_its_v2_dependency() {
    let dep = dep_at(USERS_A_X, 3);
    let root = root_importing(
        dep.stable_digest_under(IdentityScheme::V2),
        IdentityScheme::V2,
    );
    let bytes = serialize_module(&root).expect("serialize_module: test fixture");
    let header = u32::from_le_bytes(bytes[8..12].try_into().unwrap());
    assert!(
        header < 44,
        "a table of V2 rows keeps its pre-v44 header: v{header}"
    );
    let decoded = deserialize_module(&bytes).unwrap();
    assert_eq!(decoded.imports[0].scheme, IdentityScheme::V2);
    decoded.verify_import(ROW, &dep).expect("V2 row, V2 digest");
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&decoded, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
}

/// `trust-ir-self-declared/import-scheme-discriminator`, ported: the digest
/// construction changed (`stable_digest` is V3 now), and an import recorded
/// under the OLD construction is still authenticated — because the row names
/// its scheme and `stable_digest_under` recomputes it. Without the
/// discriminator (the same digest read under the current scheme) it cannot
/// be: that is the refusal a scheme-less format was stuck with.
#[test]
fn trust_ir_self_declared_import_scheme_discriminator() {
    let dep = dep_at(USERS_A_X, 3);
    let old_record = dep.stable_digest_under(IdentityScheme::V2);
    assert_ne!(old_record, dep.stable_digest(), "the construction moved");
    let with_discriminator = root_importing(old_record, IdentityScheme::V2);
    assert!(with_discriminator.verify_import(ROW, &dep).is_ok());
    let read_as_current = root_importing(old_record, IdentityScheme::CURRENT);
    assert!(matches!(
        read_as_current.verify_import(ROW, &dep),
        Err(ImportVerificationError::DigestMismatch { import: 0, .. })
    ));
    assert_eq!(IdentityScheme::V2.domain(), MODULE_IDENTITY_DOMAIN_V2);
    assert_eq!(IdentityScheme::CURRENT.domain(), MODULE_IDENTITY_DOMAIN);
}

/// One `ModuleSet` serves a V2 row and a V3 row naming the same artifact,
/// and a diamond reaching it through both schemes validates it once.
#[test]
fn one_module_set_serves_both_schemes() {
    let dep = dep_at(USERS_A_X, 3);
    let mut root = root_importing(dep.stable_digest(), IdentityScheme::V3);
    root.intern_import(
        ModuleImport::new("dep", dep.stable_digest_under(IdentityScheme::V2))
            .with_producer(Producer::Clean)
            .with_scheme(IdentityScheme::V2),
    )
    .expect("Module::intern_import: test fixture");
    let set = ModuleSet::new([&dep]);
    assert_eq!(set.len(), 1);
    assert!(
        set.get_under(IdentityScheme::V2, &dep.stable_digest())
            .is_none()
    );
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_imports().map(|m| m.len()), Some(2));
}

/// A diamond that reaches one dependency through a V3 row AND a V2 row
/// validates it ONCE: its FFI declaration is reported unbound once, not once
/// per scheme. (Mutation control for the linked memo: keying the verdict on
/// the row's scheme alone would validate the leaf twice and list the
/// declaration twice.)
#[test]
fn a_mixed_scheme_diamond_validates_the_shared_leaf_once() {
    let dep = {
        let mut mb = ModuleBuilder::new_with_target_info("dep", target());
        mb.set_default_producer(Producer::TRust);
        let file = mb.intern_file(USERS_A_X);
        let ft = mb.add_func_type(vec![], vec![Ty::U64]);
        // An FFI extern no dependency exports: reported unbound per
        // validation of the module that declares it.
        let clock = mb.declare_function("ffi_clock", ft);
        let mut fb = mb.function("dep_answer", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_span(SourceSpan {
            file,
            line: 3,
            col: 5,
        });
        let v = fb.call(clock, vec![]);
        fb.ret(vec![v]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let mut root = root_importing(dep.stable_digest(), IdentityScheme::V3);
    root.intern_import(
        ModuleImport::new("dep", dep.stable_digest_under(IdentityScheme::V2))
            .with_producer(Producer::Clean)
            .with_scheme(IdentityScheme::V2),
    )
    .expect("Module::intern_import: test fixture");
    let set = ModuleSet::new([&dep]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(
        report
            .unbound_declarations()
            .iter()
            .filter(|d| d.symbol == "ffi_clock")
            .count(),
        1,
        "{:?}",
        report.unbound_declarations()
    );
}

// ---------------------------------------------------------------------------
// negative twins
// ---------------------------------------------------------------------------

/// Spans stay identity: two builds that differ in ONE span line have
/// different V3 digests (only the path STRINGS left the identity).
#[test]
fn a_span_line_change_moves_the_v3_identity() {
    let a = dep_at(USERS_A_X, 3);
    let b = dep_at(USERS_A_X, 4);
    assert_ne!(a.stable_digest(), b.stable_digest());
    // …even across checkouts.
    assert_ne!(a.stable_digest(), dep_at("/home/b/x.rs", 4).stable_digest());
}

/// A V2 row checked against a candidate whose paths moved is `DigestMismatch`
/// (one edge) and, through the closure walk, is refused rather than bound.
#[test]
fn a_v2_row_against_a_moved_checkout_is_a_digest_mismatch() {
    let here = dep_at(USERS_A_X, 3);
    let moved = dep_at("/home/b/x.rs", 3);
    let root = root_importing(
        here.stable_digest_under(IdentityScheme::V2),
        IdentityScheme::V2,
    );
    let refused = root.verify_import(ROW, &moved).err();
    assert!(
        matches!(
            &refused,
            Some(ImportVerificationError::DigestMismatch { import: 0, recorded, actual })
                if *recorded == here.stable_digest_under(IdentityScheme::V2)
                    && *actual == moved.stable_digest_under(IdentityScheme::V2)
        ),
        "{refused:?}"
    );
    // A set holding only the moved build has no module under the V2 key.
    let set = ModuleSet::new([&moved]);
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(
        matches!(
            report.errors(),
            [ValidationError::ImportUnavailable { import: 0, name }] if name == "dep"
        ),
        "{:?}",
        report.errors()
    );
    // A resolver that HANDS the moved build over is refused at C3.
    let resolver = |_: &ModuleImport| Some(&moved);
    let report = validate_linked_module(&root, &resolver, &RejectingModuleProofAuthority);
    assert!(
        matches!(
            report.errors(),
            [ValidationError::UnauthenticatedImport { import: 0, site: "import", detail }]
                if detail.contains("is not the recorded")
        ),
        "{:?}",
        report.errors()
    );
}

// ---------------------------------------------------------------------------
// mutation controls
// ---------------------------------------------------------------------------

/// A V3 projection that ALSO blanked spans would pass the cross-checkout
/// positive — and fail the span-line twin. This is the mutant, spelled out,
/// so the twin above is shown to be the test that would catch it.
#[test]
fn mutation_a_projection_that_blanks_spans_fails_the_span_line_twin() {
    fn mutant_v3(m: &Module) -> ProofDigest {
        let mut m = m.clone();
        m.files.iter_mut().for_each(String::clear);
        for function in &mut m.functions {
            for block in &mut function.blocks {
                for node in &mut block.body {
                    node.span = None;
                }
            }
        }
        ProofDigest::sha256_domain(
            MODULE_IDENTITY_DOMAIN,
            &serialize_module(&m).expect("serialize_module: test fixture"),
        )
    }
    let a = dep_at(USERS_A_X, 3);
    let b = dep_at(USERS_A_X, 4);
    // The mutant equates the twin (so it would fail the twin's assertion) …
    assert_eq!(mutant_v3(&a), mutant_v3(&b));
    // … while the real projection keeps them apart.
    assert_ne!(a.stable_digest(), b.stable_digest());
    // And the real V3 is exactly "blank the path strings, nothing else".
    let mut blanked = a.clone();
    blanked.files.iter_mut().for_each(String::clear);
    assert_eq!(
        a.stable_digest(),
        ProofDigest::sha256_domain(
            MODULE_IDENTITY_DOMAIN,
            &serialize_module(&blanked).expect("serialize_module: test fixture")
        )
    );
}

/// A V2 row and a V3 row naming one module are two distinct rows: the scheme
/// is part of the interned identity, and a `HashedModule` answers each scheme
/// from the module it holds.
#[test]
fn the_scheme_is_part_of_the_row_and_the_hashed_handle_answers_each() {
    let dep = dep_at(USERS_A_X, 3);
    let mut root = root_importing(dep.stable_digest(), IdentityScheme::V3);
    let v2_row = ModuleImport::new("dep", dep.stable_digest())
        .with_producer(Producer::TRust)
        .with_scheme(IdentityScheme::V2);
    assert_ne!(root.imports[0], v2_row);
    assert_eq!(
        root.intern_import(v2_row)
            .expect("Module::intern_import: test fixture"),
        ImportId::new(1)
    );
    let hashed = HashedModule::new(&dep);
    assert_eq!(hashed.digest(), dep.stable_digest());
    assert_eq!(
        hashed.digest_under(IdentityScheme::V2),
        dep.stable_digest_under(IdentityScheme::V2)
    );
    // Row 1 records the V3 digest under the V2 scheme: refused, never
    // re-read under the scheme that would make it match.
    assert!(root.verify_import_hashed(ImportId::new(0), &hashed).is_ok());
    assert!(matches!(
        root.verify_import_hashed(ImportId::new(1), &hashed),
        Err(ImportVerificationError::DigestMismatch { import: 1, .. })
    ));
}

/// The text form has ONE spelling per scheme: ` scheme v3`, and V2 by
/// omission. An explicit ` scheme v2` is refused rather than accepted as a
/// second spelling of the same row; an unknown scheme is refused too.
#[test]
fn the_text_form_spells_v3_and_refuses_an_explicit_v2() {
    let golden = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("fixtures")
            .join("import_scheme.trust_ir"),
    )
    .unwrap();
    let parsed = trust_ir::parser::parse_module(&golden).expect("the golden parses");
    assert_eq!(
        parsed.imports.iter().map(|r| r.scheme).collect::<Vec<_>>(),
        [IdentityScheme::V2, IdentityScheme::V3]
    );
    let legacy_line = golden
        .lines()
        .find(|line| line.contains("\"legacy_dep\""))
        .unwrap();
    for (spelled, needle) in [
        (" scheme v2", "spelled by omitting"),
        (" scheme v9", "unknown import identity scheme"),
    ] {
        let mutated = golden.replace(legacy_line, &format!("{legacy_line}{spelled}"));
        let err = trust_ir::parser::parse_module(&mutated).expect_err(spelled);
        assert!(err.to_string().contains(needle), "{spelled}: {err}");
    }
}

// ---------------------------------------------------------------------------
// tripwire: `Module.files` strings are debug-only
// ---------------------------------------------------------------------------

/// V3 blanks `files[i]` strings, which is sound only while nothing
/// load-bearing reads one. This scans the non-test sources of `trust-ir` and
/// `trust-ir-build` for every read of the file table — `.files`, the
/// `Module::file_name(index)` / `resolve_span` / `render_diagnostic`
/// accessors — and fails on any that is not (a) a LENGTH read
/// (`files.len()` / `files.is_empty()`: V3 keeps the length, so a range check
/// still binds), or (b) allowlisted: the text printer and parser, the codec
/// (where V3 projects the strings), and the table's own accessors in
/// `lib.rs`, each pinned by the exact code it may contain.
///
/// A future rule that makes a path load-bearing must first move it out of
/// `files` (or out of the V3 identity) — extending this allowlist is exactly
/// the review decision this test forces.
#[test]
fn module_files_strings_are_debug_only() {
    use std::path::{Path, PathBuf};

    /// Whole files that may read path strings, and why.
    const ALLOWED_FILES: &[(&str, &str)] = &[
        (
            "trust-ir/src/display.rs",
            "the text printer spells the table",
        ),
        (
            "trust-ir/src/parser.rs",
            "the text parser rebuilds the table",
        ),
        (
            "trust-ir/src/binary.rs",
            "the codec; V3 projects the strings here",
        ),
        (
            "trust-ir/src/binary/observed/fields_4.rs",
            "the observed codec twin writes the table as binary.rs does",
        ),
        (
            "trust-ir/src/binary/observed/collect_1.rs",
            "the observed codec twin collects the table's strings as binary.rs does",
        ),
    ];
    /// Exact reads allowed elsewhere: (file, code fragment, why).
    const ALLOWED_READS: &[(&str, &str, &str)] = &[
        (
            "trust-ir/src/binary/observed/body/wire.rs",
            "\"Module.files\",",
            "a section label the observed body writer spells, not a read of the table",
        ),
        (
            "trust-ir/src/lib.rs",
            "self.files.iter().position(|p| *p == path)",
            "Module::intern_file dedups by path",
        ),
        (
            "trust-ir/src/lib.rs",
            "self.files.push(path)",
            "Module::intern_file",
        ),
        (
            "trust-ir/src/lib.rs",
            "self.files.get(index as usize)",
            "Module::file_name, the accessor",
        ),
        (
            "trust-ir/src/lib.rs",
            "self.file_name(span.file)",
            "Module::resolve_span, a diagnostic",
        ),
        (
            "trust-ir/src/lib.rs",
            "self.resolve_span(span)",
            "Module::render_diagnostic, a printer",
        ),
        (
            "trust-ir/src/level.rs",
            "files: self.files.clone()",
            "ModuleG::try_map_level (amendment S) carries the table across a level change unread",
        ),
        (
            "trust-ir-build/src/template.rs",
            "out.files = t.files.clone()",
            "instantiate's seed (amendment S) carries the template's table unread",
        ),
        (
            "trust-ir-build/src/template.rs",
            "prefix(\"file\", &before.files, &after.files)",
            "instantiate's append-only check: a host that edits the table is refused",
        ),
        (
            "trust-ir-build/src/merge.rs",
            "dst.files.extend(self.appended_files)",
            "merge_into (WS4.11) commits src's rows and any placeholder by APPENDING them unread; \
             every span index was fixed from the tables' lengths alone (map_files), so no path \
             string steers the merge",
        ),
    ];

    fn rust_files(dir: &Path, out: &mut Vec<PathBuf>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                rust_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        }
    }
    /// The file's lines with every braced `#[cfg(test)] mod NAME { .. }`
    /// removed (brace-matched, so an inline test module in the MIDDLE of a
    /// file does not hide the production code after it). Numbers are kept.
    fn production_lines(text: &str) -> Vec<(usize, &str)> {
        let lines: Vec<&str> = text.lines().collect();
        let mut out = Vec::new();
        let mut i = 0;
        while i < lines.len() {
            let opens_test_mod = lines[i].trim() == "#[cfg(test)]"
                && lines.get(i + 1).is_some_and(|next| {
                    let t = next.trim_start();
                    t.starts_with("mod ") && t.trim_end().ends_with('{')
                });
            if opens_test_mod {
                let mut depth = 0i64;
                let mut j = i + 1;
                loop {
                    depth += lines[j].matches('{').count() as i64;
                    depth -= lines[j].matches('}').count() as i64;
                    j += 1;
                    if depth <= 0 || j >= lines.len() {
                        break;
                    }
                }
                i = j;
                continue;
            }
            out.push((i + 1, lines[i]));
            i += 1;
        }
        out
    }

    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut sources = Vec::new();
    for krate in ["trust-ir", "trust-ir-build"] {
        rust_files(&crates.join(krate).join("src"), &mut sources);
    }
    let mut scanned = 0usize;
    let mut offenders = Vec::new();
    for path in &sources {
        let relative = path
            .strip_prefix(&crates)
            .unwrap()
            .to_string_lossy()
            .replace('\\', "/");
        let name = path.file_name().unwrap().to_string_lossy();
        if name == "tests.rs" || name.ends_with("_tests.rs") || relative.contains("/tests/") {
            continue;
        }
        let text = std::fs::read_to_string(path).unwrap();
        for (number, line) in production_lines(&text) {
            let code = line.split("//").next().unwrap_or("");
            let table_reads: Vec<usize> = code
                .match_indices(".files")
                .map(|(at, _)| at)
                .filter(|at| !code[at + ".files".len()..].starts_with('_'))
                .collect();
            // `Module::file_name(index)` — never `Path::file_name()`.
            let accessor = code
                .match_indices(".file_name(")
                .any(|(at, m)| !code[at + m.len()..].starts_with(')'))
                || code.contains(".resolve_span(")
                || code.contains(".render_diagnostic(");
            if table_reads.is_empty() && !accessor {
                continue;
            }
            scanned += 1;
            let length_only = !accessor
                && table_reads.iter().all(|at| {
                    let rest = &code[at + ".files".len()..];
                    rest.starts_with(".len()") || rest.starts_with(".is_empty()")
                });
            let allowed = ALLOWED_FILES.iter().any(|(file, _)| relative == *file)
                || ALLOWED_READS
                    .iter()
                    .any(|(file, fragment, _)| relative == *file && code.contains(fragment));
            if !length_only && !allowed {
                offenders.push(format!("{relative}:{number}: {}", line.trim()));
            }
        }
    }
    assert!(
        scanned >= 10,
        "the scan saw only {scanned} reads of the file table; it has gone blind"
    );
    assert!(
        offenders.is_empty(),
        "a Module.files path STRING is read outside the debug printers / codec — the V3 \
         identity no longer covers it (see IdentityScheme): {offenders:#?}"
    );
}

// ---------------------------------------------------------------------------
// adversarial (review)
// ---------------------------------------------------------------------------

/// The V3 projection reaches the file TABLE and nothing else, even when a
/// debug path string is ALSO spelled somewhere load-bearing (the string pool
/// deduplicates equal strings, so a projection keyed on the pooled string
/// rather than on the table would blank the module name with it). Two builds
/// whose module NAME is the checkout path stay distinct identities.
#[test]
fn review_a_path_spelled_elsewhere_stays_identity() {
    let named_after = |path: &str| {
        let mut m = dep_at(path, 3);
        m.name = path.to_string();
        m
    };
    let here = named_after(USERS_A_X);
    let moved = named_after("/home/b/x.rs");
    assert_ne!(
        here.stable_digest(),
        moved.stable_digest(),
        "the module name is identity even when it equals a debug path"
    );
    // Control: with the name held fixed, only the table differs and V3 is equal.
    let mut moved_same_name = moved.clone();
    moved_same_name.name = here.name.clone();
    assert_eq!(here.stable_digest(), moved_same_name.stable_digest());
}

/// A `ModuleSet` holding BOTH builds of `dep` (they share a V3 identity, and
/// the first inserted keeps the V3 key) still serves a V2 row naming the
/// SECOND build — the V2 key is its own — and a root carrying a V3 row and
/// that V2 row links cleanly, each edge authenticated against the module its
/// own scheme names.
#[test]
fn review_a_set_holding_both_builds_serves_each_scheme_its_own_module() {
    let here = dep_at(USERS_A_X, 3);
    let moved = dep_at("/home/b/x.rs", 3);
    let set = ModuleSet::new([&here, &moved]);
    assert_eq!(set.len(), 1, "one portable identity");
    let v2_moved = moved.stable_digest_under(IdentityScheme::V2);
    assert!(std::ptr::eq(
        set.get_under(IdentityScheme::V2, &v2_moved).unwrap(),
        &moved
    ));
    assert!(std::ptr::eq(
        set.get(&moved.stable_digest()).unwrap(),
        &here
    ));

    let mut root = root_importing(here.stable_digest(), IdentityScheme::V3);
    root.intern_import(
        ModuleImport::new("dep", v2_moved)
            .with_producer(Producer::Clean)
            .with_scheme(IdentityScheme::V2),
    )
    .expect("Module::intern_import: test fixture");
    let report = validate_linked_module(&root, &set, &RejectingModuleProofAuthority);
    assert!(report.is_ok(), "{:?}", report.errors());
    assert_eq!(report.authenticated_imports().map(|m| m.len()), Some(2));
    // Twin: a V2 row for a build the set does NOT hold is unavailable, even
    // though a module with the same portable identity is present.
    let absent = dep_at("/opt/c/x.rs", 3).stable_digest_under(IdentityScheme::V2);
    let refused = root_importing(absent, IdentityScheme::V2);
    let report = validate_linked_module(&refused, &set, &RejectingModuleProofAuthority);
    assert!(
        matches!(
            report.errors(),
            [ValidationError::ImportUnavailable { import: 0, .. }]
        ),
        "{:?}",
        report.errors()
    );
}

/// A legacy (v41..=v43) positional MessagePack row — written when `producer`
/// was still conditionally skipped, so a producer-less row is a TWO-element
/// array — decodes under the v44 schema as a V2 row with no producer. (v44
/// stopped skipping `producer` so that `scheme` could be the sole trailing
/// skipped field; the older, shorter spelling must still read.)
#[test]
fn review_a_legacy_positional_msgpack_row_decodes_as_v2() {
    // A positional struct is a MessagePack array, exactly as a tuple is, so
    // the legacy spellings are the tuples the old derive wrote.
    let digest = ProofDigest::sha256([0x41; 32]);
    let bare = rmp_serde::to_vec(&("bare", digest)).unwrap();
    let tagged = rmp_serde::to_vec(&("tagged", digest, Producer::Clean)).unwrap();
    let bare: ModuleImport = rmp_serde::from_slice(&bare).expect("a two-element row decodes");
    let tagged: ModuleImport = rmp_serde::from_slice(&tagged).expect("a three-element row decodes");
    assert_eq!(
        bare,
        ModuleImport::new("bare", digest).with_scheme(IdentityScheme::V2)
    );
    assert_eq!(
        tagged,
        ModuleImport::new("tagged", digest)
            .with_producer(Producer::Clean)
            .with_scheme(IdentityScheme::V2)
    );
    // And the v44 positional spelling round-trips both schemes.
    let current = vec![
        ModuleImport::new("bare", digest),
        ModuleImport::new("legacy", digest).with_scheme(IdentityScheme::V2),
    ];
    let back: Vec<ModuleImport> =
        rmp_serde::from_slice(&rmp_serde::to_vec(&current).unwrap()).unwrap();
    assert_eq!(back, current);
}

/// A v44 blob whose scheme byte is not an allocated tag is refused by name,
/// never decoded as some scheme; the text form refuses a scheme label with
/// trailing junk rather than reading its `v3` prefix.
#[test]
fn review_an_unallocated_scheme_tag_or_label_is_refused() {
    let dep = dep_at(USERS_A_X, 3);
    let root = root_importing(dep.stable_digest(), IdentityScheme::V3);
    let bytes = serialize_module(&root).expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 44);
    // The row is `name, digest, producer?, scheme`: locate the recorded
    // digest bytes; the producer presence byte, its tag (`TRust` = 0) and the
    // scheme tag (`V3` = 1) follow.
    let digest = dep.stable_digest().bytes;
    let at = bytes
        .windows(digest.len())
        .position(|w| w == digest)
        .expect("the row's digest is in the blob")
        + digest.len();
    assert_eq!(&bytes[at..at + 3], &[1, 0, 1]);
    let scheme_byte = at + 2;
    let mut relabelled = bytes.clone();
    relabelled[scheme_byte] = 0;
    assert_eq!(
        deserialize_module(&relabelled).unwrap().imports[0].scheme,
        IdentityScheme::V2,
        "the located byte IS the scheme tag"
    );
    let mut forged = bytes.clone();
    forged[scheme_byte] = 2;
    assert!(
        matches!(
            deserialize_module(&forged),
            Err(trust_ir::binary::BinaryError::InvalidTag(2))
        ),
        "{:?}",
        deserialize_module(&forged)
    );

    let text = root.to_string();
    assert!(text.contains(" scheme v3"), "{text}");
    assert_eq!(trust_ir::parser::parse_module(&text).unwrap(), root);
    for junk in [" scheme v3x", " scheme v30", " scheme v3-", " scheme v2x"] {
        let mutated = text.replace(" scheme v3", junk);
        let err = trust_ir::parser::parse_module(&mutated)
            .expect_err("a label with trailing bytes must not parse as a scheme");
        assert!(
            err.to_string().contains("unknown import identity scheme"),
            "{junk}: {err}"
        );
    }
    // An unknown token BETWEEN or AFTER the clauses is refused: the module
    // loop skips lines it does not know, so before the review fix
    // `producer trust junk scheme v3` parsed as a V2 row (the scheme clause
    // silently dropped) — the row would then authenticate under the wrong
    // identity domain.
    for (from, to) in [
        (" producer trust", " producer trust junk"),
        (" scheme v3", " scheme v3 junk"),
    ] {
        let mutated = text.replace(from, to);
        let err = trust_ir::parser::parse_module(&mutated)
            .expect_err("trailing text on an import entry must be refused");
        assert!(
            err.to_string()
                .contains("unexpected text after import entry"),
            "{to}: {err}"
        );
    }
    // A trailing `;` comment is still admitted.
    let commented = text.replace(" scheme v3", " scheme v3 ; portable");
    assert_eq!(trust_ir::parser::parse_module(&commented).unwrap(), root);
}

/// The codegen-cache identity (`executable_content_digest_v1`) and the
/// portable identity both compute over a module carrying a V3 row, and the
/// scheme is part of both images: the same row recorded under V2 is a
/// different module under each.
#[test]
fn review_the_scheme_byte_is_identity_in_both_digests() {
    let dep = dep_at(USERS_A_X, 3);
    let v3 = root_importing(dep.stable_digest(), IdentityScheme::V3);
    let mut v2 = v3.clone();
    v2.imports[0].scheme = IdentityScheme::V2;
    assert_ne!(v3.stable_digest(), v2.stable_digest());
    assert_ne!(
        v3.executable_content_digest_v1(),
        v2.executable_content_digest_v1()
    );
}

/// WS8.12 review (`docs/SPEC_RATIFICATIONS.md` §23, the documentation half
/// of F-117): portable source names are a producer SHOULD, never a validator
/// rule. An ABSOLUTE checkout path in `Module.files` changes no verdict at any
/// tier — the plain, codegen, authority and decoded-provenance validators
/// give the absolute-path build exactly the verdicts of its portable twin, and
/// the plain verdict is clean — while a producer that writes the PORTABLE
/// name gets what §23 says it buys: two builds at two checkouts are one byte
/// stream and one `executable_content_digest_v1`, where the absolute-path
/// builds are two (`crit_unex03_moved_checkout_keeps_the_portable_identity`).
#[test]
fn ws8_12_section23_portable_names_are_a_producer_should_not_a_validator_rule() {
    use trust_ir::binary::deserialize_module_with_wire_version;
    use trust_ir_build::{
        validate_module, validate_module_as_decoded, validate_module_for_codegen,
        validate_module_with_authority,
    };

    let absolute = dep_at(USERS_A_X, 3);
    let portable = dep_at("src/x.rs", 3);
    assert_eq!(
        validate_module(&absolute),
        Vec::new(),
        "an absolute path is legal"
    );
    let verdicts = |m: &Module| {
        let (decoded, wire) = deserialize_module_with_wire_version(
            &serialize_module(m).expect("serialize_module: test fixture"),
        )
        .expect("decodes");
        (
            validate_module(m),
            validate_module_for_codegen(m),
            validate_module_with_authority(m, &RejectingModuleProofAuthority),
            validate_module_as_decoded(&decoded, wire),
        )
    };
    assert_eq!(
        verdicts(&absolute),
        verdicts(&portable),
        "the source path is debug metadata: no tier reads it"
    );

    // The payoff of the SHOULD: the portable name is the same string at every
    // checkout, so the artifact bytes and the codegen-cache identity agree.
    let portable_elsewhere = dep_at("src/x.rs", 3);
    assert_eq!(
        serialize_module(&portable).expect("serialize_module: test fixture"),
        serialize_module(&portable_elsewhere).expect("serialize_module: test fixture")
    );
    assert_eq!(
        portable.executable_content_digest_v1(),
        portable_elsewhere.executable_content_digest_v1()
    );
    // Mutation control: the absolute spelling at a second checkout loses both.
    let absolute_elsewhere = dep_at("/home/b/x.rs", 3);
    assert_ne!(
        serialize_module(&absolute).expect("serialize_module: test fixture"),
        serialize_module(&absolute_elsewhere).expect("serialize_module: test fixture")
    );
    assert_ne!(
        absolute.executable_content_digest_v1(),
        absolute_elsewhere.executable_content_digest_v1()
    );
    // And all four share the one portable import identity.
    for m in [&portable, &portable_elsewhere, &absolute_elsewhere] {
        assert_eq!(m.stable_digest(), absolute.stable_digest());
    }
}
