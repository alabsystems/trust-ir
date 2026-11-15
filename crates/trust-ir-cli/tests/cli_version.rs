// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Roadmap WS8.4 (F-118, the version-string half): every tool's `--version`
//! carries a build identity, `<name> <MAJOR.MINOR.0>+<source>`.
//!
//! Two halves:
//!
//! * the shipped binary: `--version`, `--version --verbose` and
//!   `version --json` report `trust_ir::BUILD_IDENTITY` — wire version, read
//!   range and module-identity domain included;
//! * the build-script rule that resolves `<source>`, driven here through the
//!   exact file `crates/trust-ir/build.rs` runs (`build_identity.rs`, included
//!   below), against a controlled environment and scratch checkouts: the
//!   packaging override is live, a malformed override fails the build naming
//!   the variable, and the `git` fallback never guesses (unrelated enclosing
//!   repository ⇒ `unknown`) and never claims a clean tree (`.local`).

mod common;

#[allow(dead_code)]
#[path = "../../trust-ir/build_identity.rs"]
mod build_identity;

use std::collections::BTreeMap;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use build_identity::{
    Attestation, ENV_GIT_DIRTY, ENV_GIT_SHA, OUT_ATTESTATION, OUT_SHA, OUT_SOURCE,
    build_directives, resolve,
};
use common::trust_ir_cmd;
use trust_ir::{BUILD_IDENTITY, SourceAttestation};

const GIT: &str = "git";

fn env_of(pairs: &[(&str, &str)]) -> impl Fn(&str) -> Option<String> + use<> {
    let map: BTreeMap<String, String> = pairs
        .iter()
        .map(|(k, v)| ((*k).to_string(), (*v).to_string()))
        .collect();
    move |key: &str| map.get(key).cloned()
}

fn stdout_of(args: &[&str]) -> String {
    let out = trust_ir_cmd().args(args).output().expect("spawn trust-ir");
    assert!(
        out.status.success(),
        "trust-ir {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("utf8 stdout")
}

/// `<pkg>+<source>` where `<source>` is `unknown` or `g<12 lowercase hex>`
/// optionally followed by `.dirty` / `.local`.
fn assert_version_shape(version: &str) {
    let (pkg, source) = version.split_once('+').expect("version has build metadata");
    assert_eq!(pkg, BUILD_IDENTITY.pkg_version);
    if source == "unknown" {
        return;
    }
    let rest = source
        .strip_prefix('g')
        .unwrap_or_else(|| panic!("source label {source:?} is neither unknown nor g<sha>"));
    let (hex, suffix) = rest.split_at(12.min(rest.len()));
    assert_eq!(hex.len(), 12, "{source:?}");
    assert!(
        hex.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "{source:?}"
    );
    assert!(matches!(suffix, "" | ".dirty" | ".local"), "{source:?}");
}

fn rustc_env(directives: &[String], key: &str) -> String {
    let prefix = format!("cargo:rustc-env={key}=");
    directives
        .iter()
        .find_map(|d| d.strip_prefix(&prefix))
        .unwrap_or_else(|| panic!("no {key} directive in {directives:?}"))
        .to_string()
}

fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new(GIT)
        .arg("-C")
        .arg(dir)
        .args([
            "-c",
            "user.name=ws84",
            "-c",
            "user.email=ws84@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "-c",
            "core.hooksPath=/dev/null",
        ])
        .args(args)
        .output()
        .expect("git is required by the WS8.4 fallback tests");
    assert!(
        out.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap().trim().to_string()
}

fn init_repo(root: &Path) {
    git(root, &["init", "-q"]);
    fs::write(root.join("README"), "unrelated repository\n").unwrap();
    git(root, &["add", "README"]);
    git(root, &["commit", "-q", "--no-verify", "-m", "one commit"]);
}

/// Copy the real crate's manifest and build-script sources to `dest`.
fn copy_crate(dest: &Path) -> PathBuf {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-ir");
    fs::create_dir_all(dest).unwrap();
    for file in ["Cargo.toml", "build.rs", "build_identity.rs"] {
        fs::copy(src.join(file), dest.join(file)).unwrap();
    }
    dest.to_path_buf()
}

/// The highest version the wire-version ledger (`crates/trust-ir/
/// wire_versions.tsv`) marks `shipped`.
fn highest_shipped_wire_version() -> u32 {
    let ledger = Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-ir/wire_versions.tsv");
    let text = fs::read_to_string(&ledger).expect("the wire-version ledger");
    text.lines()
        .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
        .filter_map(|line| {
            let mut columns = line.split('\t');
            let version = columns.next()?.trim().parse::<u32>().ok()?;
            (columns.next()?.trim() == "shipped").then_some(version)
        })
        .max()
        .expect("the ledger has a shipped row")
}

// ---------------------------------------------------------------------------
// The shipped binary
// ---------------------------------------------------------------------------

#[test]
fn version_names_wire_and_domain() {
    // `--version`: one line, the publication dev-build shape.
    let short = stdout_of(&["--version"]);
    assert_eq!(short, format!("trust-ir {}\n", BUILD_IDENTITY.version));
    assert_version_shape(BUILD_IDENTITY.version);
    assert_eq!(stdout_of(&["-V"]), short);

    // `--version --verbose` and `version`: wire version and digest domain.
    let verbose = stdout_of(&["--version", "--verbose"]);
    assert!(verbose.starts_with(&short), "{verbose}");
    // Derived, never a spelled number (a wire bump must not be a line every
    // parallel addition edits) — but from an INDEPENDENT source: the highest
    // `shipped` row of the wire-version ledger, not the build identity the
    // CLI itself prints (which is `binary::VERSION`).
    let wire = highest_shipped_wire_version();
    assert_eq!(
        BUILD_IDENTITY.wire_version, wire,
        "the build ships the ledger's version"
    );
    assert!(verbose.contains(&format!("wire v{wire}")), "{verbose}");
    assert!(verbose.contains("trust_ir.module.v3"), "{verbose}");
    assert!(
        verbose.contains(&format!(
            "v23..=v25, v29..=v{wire} (v26..=v28 refused: ambiguous lineage)"
        )),
        "{verbose}"
    );
    assert!(verbose.contains(BUILD_IDENTITY.source_sha), "{verbose}");
    assert_eq!(stdout_of(&["version"]), verbose);

    // `version --json`: the same facts, machine-readable.
    let json: serde_json::Value =
        serde_json::from_str(&stdout_of(&["version", "--json"])).expect("valid JSON");
    assert_eq!(json["name"], "trust-ir");
    assert_eq!(json["version"], BUILD_IDENTITY.version);
    assert_eq!(json["wire_version"], wire);
    assert_eq!(json["min_read_version"], 23);
    assert_eq!(json["refused_read_versions"], serde_json::json!([26, 28]));
    assert_eq!(json["digest_domain"], "trust_ir.module.v3");
    assert_eq!(json["attestation"], BUILD_IDENTITY.attestation.as_str());
    let readable: Vec<u64> = json["readable_wire_versions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_u64().unwrap())
        .collect();
    let expected: Vec<u64> = (23..=25).chain(29..=u64::from(wire)).collect();
    assert_eq!(readable, expected);
    if BUILD_IDENTITY.attestation == SourceAttestation::Unknown {
        assert!(json["source_sha"].is_null());
    } else {
        assert_eq!(json["source_sha"], BUILD_IDENTITY.source_sha);
    }

    // `--verbose` alone is not a version request, and `--version` does not
    // combine with a subcommand.
    let out = trust_ir_cmd().arg("--verbose").output().unwrap();
    assert!(!out.status.success());
    let out = trust_ir_cmd()
        .args(["--version", "dump", "x.json"])
        .output()
        .unwrap();
    assert!(!out.status.success());

    // The packaging override is live: the directives `build.rs` prints for
    // `ALAB_BUILD_GIT_SHA=0123456789ab ALAB_BUILD_GIT_DIRTY=0` name exactly
    // that sha, unqualified, so the compiled version is `<pkg>+g0123456789ab`.
    let env = env_of(&[(ENV_GIT_SHA, "0123456789ab"), (ENV_GIT_DIRTY, "0")]);
    let tmp = tempfile::tempdir().unwrap();
    let directives =
        build_directives(&env, tmp.path(), OsStr::new("/nonexistent/git")).expect("valid override");
    assert_eq!(rustc_env(&directives, OUT_SOURCE), "g0123456789ab");
    assert_eq!(rustc_env(&directives, OUT_SHA), "0123456789ab");
    assert_eq!(rustc_env(&directives, OUT_ATTESTATION), "packaged-clean");
    assert!(directives.contains(&format!("cargo:rerun-if-env-changed={ENV_GIT_SHA}")));
    assert!(directives.contains(&format!("cargo:rerun-if-env-changed={ENV_GIT_DIRTY}")));
    let version = format!(
        "{}+{}",
        BUILD_IDENTITY.pkg_version,
        rustc_env(&directives, OUT_SOURCE)
    );
    assert!(version.ends_with("+g0123456789ab"), "{version}");
    assert_version_shape(&version);

    // A 40-hex override is abbreviated to 12; a dirty attestation says so.
    let full = "0123456789abcdef0123456789abcdef01234567";
    let env = env_of(&[(ENV_GIT_SHA, full), (ENV_GIT_DIRTY, "1")]);
    let id = resolve(&env, tmp.path(), OsStr::new(GIT)).unwrap();
    assert_eq!(id.attestation, Attestation::PackagedDirty);
    assert_eq!(id.label(), "g0123456789ab.dirty");
    assert_eq!(id.sha.as_deref(), Some(full));

    // `build.rs` is a thin printer of these directives: it prints every line
    // and fails the build on an error. A build.rs that swallowed the error
    // would turn the negative twin below into a silent `unknown`.
    let build_rs =
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-ir/build.rs"))
            .unwrap();
    assert!(build_rs.contains("build_identity::build_directives("));
    assert!(build_rs.contains("println!(\"{line}\")"));
    assert!(build_rs.contains("Err(error) => panic!("));
}

#[test]
fn every_tool_prints_the_build_identity() {
    // The two thin tools shipped beside `trust-ir` are separate packages; their
    // binaries are not built for this crate's tests, so pin their source: each
    // prints `BUILD_IDENTITY.version` and const-asserts the shared release.
    for (tool, file) in [
        ("trust-ir-fmt", "../trust-ir-fmt/src/main.rs"),
        ("trust-ir-diff", "../trust-ir-diff/src/main.rs"),
    ] {
        let src = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(file)).unwrap();
        assert!(
            src.contains(&format!(
                "println!(\"{tool} {{}}\", trust_ir::BUILD_IDENTITY.version)"
            )),
            "{tool} --version must print BUILD_IDENTITY.version"
        );
        assert!(
            src.contains("trust_ir::BUILD_IDENTITY.has_pkg_version(env!(\"CARGO_PKG_VERSION\"))"),
            "{tool} must const-assert the shared package version"
        );
    }
}

// ---------------------------------------------------------------------------
// Negative twin: a malformed override FAILS the build, naming the variable
// ---------------------------------------------------------------------------

#[test]
fn malformed_override_fails_the_build_naming_the_variable() {
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let run = |pairs: &[(&str, &str)]| {
        build_directives(&env_of(pairs), dir, OsStr::new(GIT))
            .expect_err("a malformed packaging override must fail the build")
    };

    // The row the roadmap names, `TRUST_BUILD_GIT_SHA=xyz`, fails naming the
    // variable. It fails before its syntax is even read: the whole `TRUST_*`
    // spelling is refused, because verified Targo scrubs `TRUST_*` from build
    // scripts and the override would silently vanish on that lane.
    let err = run(&[
        ("TRUST_BUILD_GIT_SHA", "xyz"),
        ("TRUST_BUILD_GIT_DIRTY", "0"),
    ]);
    assert!(err.starts_with("TRUST_BUILD_GIT_SHA is not read"), "{err}");
    assert!(err.contains("set ALAB_BUILD_GIT_SHA instead"), "{err}");

    // The same syntax error under the live spelling: malformed, by name.
    let err = run(&[(ENV_GIT_SHA, "xyz"), (ENV_GIT_DIRTY, "0")]);
    assert!(
        err.contains("ALAB_BUILD_GIT_SHA=\"xyz\" is malformed"),
        "{err}"
    );
    let err = run(&[(ENV_GIT_SHA, "xyz")]);
    assert!(
        err.contains("ALAB_BUILD_GIT_SHA=\"xyz\" is malformed"),
        "{err}"
    );

    // A value that is not valid Unicode is malformed by name, never read as
    // unset (which would fall through to git).
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt;
        let raw = std::ffi::OsString::from_vec(b"0123456789a\xff".to_vec());
        let value = build_identity::env_value(Some(raw)).expect("present stays present");
        let err = run(&[(ENV_GIT_SHA, value.as_str()), (ENV_GIT_DIRTY, "0")]);
        assert!(err.starts_with("ALAB_BUILD_GIT_SHA="), "{err}");
        assert!(err.contains("is malformed"), "{err}");
        let raw = std::ffi::OsString::from_vec(b"\xff".to_vec());
        let value = build_identity::env_value(Some(raw)).unwrap();
        let err = run(&[
            (ENV_GIT_SHA, "0123456789ab"),
            (ENV_GIT_DIRTY, value.as_str()),
        ]);
        assert!(err.starts_with("ALAB_BUILD_GIT_DIRTY="), "{err}");
    }
    assert_eq!(build_identity::env_value(None), None);

    // Uppercase, too short, too long, empty: all malformed, never truncated
    // or normalised into something that looks attested.
    for bad in [
        "0123456789AB",
        "0123456789a",
        "0123456789abcdef0123456789abcdef012345678",
        "",
        " 0123456789ab",
    ] {
        let err = run(&[(ENV_GIT_SHA, bad), (ENV_GIT_DIRTY, "0")]);
        assert!(err.starts_with("ALAB_BUILD_GIT_SHA="), "{bad:?}: {err}");
        assert!(err.contains("is malformed"), "{bad:?}: {err}");
    }

    // The dirty flag is part of the attestation: malformed, missing, or
    // present without a sha, each fails naming the variable.
    let err = run(&[(ENV_GIT_SHA, "0123456789ab"), (ENV_GIT_DIRTY, "yes")]);
    assert!(
        err.contains("ALAB_BUILD_GIT_DIRTY=\"yes\" is malformed"),
        "{err}"
    );
    let err = run(&[(ENV_GIT_SHA, "0123456789ab")]);
    assert!(
        err.contains("ALAB_BUILD_GIT_SHA is set but ALAB_BUILD_GIT_DIRTY is not"),
        "{err}"
    );
    let err = run(&[(ENV_GIT_DIRTY, "0")]);
    assert!(
        err.contains("ALAB_BUILD_GIT_DIRTY=\"0\" is set but ALAB_BUILD_GIT_SHA is not"),
        "{err}"
    );
}

#[test]
fn trust_prefixed_override_is_refused_by_name() {
    // A well-formed override under the draft `TRUST_*` spelling is refused,
    // never honoured: honouring it would make the embedded identity depend on
    // the Targo lane (verified Targo scrubs `TRUST_*` from build scripts).
    let tmp = tempfile::tempdir().unwrap();
    let dir = tmp.path();
    let run = |pairs: &[(&str, &str)]| build_directives(&env_of(pairs), dir, OsStr::new(GIT));

    let err = run(&[
        ("TRUST_BUILD_GIT_SHA", "0123456789ab"),
        ("TRUST_BUILD_GIT_DIRTY", "0"),
    ])
    .expect_err("the TRUST_* spelling must fail the build");
    assert!(err.starts_with("TRUST_BUILD_GIT_SHA is not read"), "{err}");
    assert!(err.contains("set ALAB_BUILD_GIT_SHA instead"), "{err}");

    // Either half alone, and alongside a valid live override: still refused,
    // so no build carries two spellings that could disagree.
    let err = run(&[("TRUST_BUILD_GIT_DIRTY", "0")]).unwrap_err();
    assert!(
        err.starts_with("TRUST_BUILD_GIT_DIRTY is not read"),
        "{err}"
    );
    assert!(err.contains("set ALAB_BUILD_GIT_DIRTY instead"), "{err}");
    let err = run(&[
        (ENV_GIT_SHA, "0123456789ab"),
        (ENV_GIT_DIRTY, "0"),
        ("TRUST_BUILD_GIT_SHA", "fedcba987654"),
    ])
    .unwrap_err();
    assert!(err.starts_with("TRUST_BUILD_GIT_SHA is not read"), "{err}");

    // Mutation control: the live spelling alone is accepted, and a later
    // `TRUST_*` setting re-runs the script so the refusal can fire.
    let directives = run(&[(ENV_GIT_SHA, "0123456789ab"), (ENV_GIT_DIRTY, "0")]).unwrap();
    assert_eq!(rustc_env(&directives, OUT_SOURCE), "g0123456789ab");
    for name in ["TRUST_BUILD_GIT_SHA", "TRUST_BUILD_GIT_DIRTY"] {
        assert!(
            directives.contains(&format!("cargo:rerun-if-env-changed={name}")),
            "{directives:?}"
        );
    }

    // `build.rs` reads the environment through `env_value`, not
    // `std::env::var(..).ok()`, which would read a non-Unicode value as unset.
    let build_rs =
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-ir/build.rs"))
            .unwrap();
    assert!(build_rs.contains("build_identity::env_value(std::env::var_os(key))"));
}

// ---------------------------------------------------------------------------
// Mutation controls: the fallback never guesses and never claims clean
// ---------------------------------------------------------------------------

#[test]
fn no_source_prints_unknown() {
    // Not in any repository, no override.
    let tmp = tempfile::tempdir().unwrap();
    let krate = copy_crate(&tmp.path().join("crates/trust-ir"));
    let id = resolve(&env_of(&[]), &krate, OsStr::new(GIT)).unwrap();
    assert_eq!(id.attestation, Attestation::Unknown);
    assert_eq!(id.sha, None);
    assert_eq!(id.label(), "unknown");

    // In its own checkout, but `git` is missing: still `unknown`, and a
    // missing `git` never fails the build.
    init_repo(tmp.path());
    git(tmp.path(), &["add", "crates"]);
    git(tmp.path(), &["commit", "-q", "--no-verify", "-m", "crate"]);
    let directives = build_directives(&env_of(&[]), &krate, OsStr::new("/nonexistent/git"))
        .expect("a missing git never fails the build");
    assert_eq!(rustc_env(&directives, OUT_SOURCE), "unknown");
    assert_eq!(rustc_env(&directives, OUT_SHA), "unknown");
    assert_eq!(rustc_env(&directives, OUT_ATTESTATION), "unknown");
    let version = format!("{}+unknown", BUILD_IDENTITY.pkg_version);
    assert_version_shape(&version);
    assert!(!directives.iter().any(|d| d.contains("+g")));
}

#[test]
fn vendored_copy_in_unrelated_repo_prints_unknown() {
    let tmp = tempfile::tempdir().unwrap();
    let repo = tmp.path();
    init_repo(repo);
    let unrelated_head = git(repo, &["rev-parse", "HEAD"]);

    // Vendored and COMMITTED somewhere other than the crate's own position.
    let vendored = copy_crate(&repo.join("third_party/vendor/trust-ir"));
    git(repo, &["add", "third_party"]);
    git(
        repo,
        &["commit", "-q", "--no-verify", "-m", "vendor trust-ir"],
    );
    let id = resolve(&env_of(&[]), &vendored, OsStr::new(GIT)).unwrap();
    assert_eq!(id.label(), "unknown", "must not report the enclosing sha");
    assert_eq!(id.sha, None);

    // Dropped at the right relative path but NOT recorded in the enclosing
    // repository's HEAD: still not this repository's source.
    let dropped = copy_crate(&repo.join("crates/trust-ir"));
    let id = resolve(&env_of(&[]), &dropped, OsStr::new(GIT)).unwrap();
    assert_eq!(id.label(), "unknown");
    let directives = build_directives(&env_of(&[]), &dropped, OsStr::new(GIT)).unwrap();
    assert!(
        !directives.iter().any(|d| d.contains(&unrelated_head[..12])),
        "{directives:?}"
    );
    assert!(!directives.iter().any(|d| d.contains("rerun-if-changed=/")));

    // Now the enclosing repository DOES record a crate at `crates/trust-ir`
    // (a monorepo). That copy is in its own checkout and reports `.local`; the
    // vendored copy elsewhere still sits below a root that is not ITS root, so
    // it stays `unknown` — the position check, not the HEAD check, decides.
    git(repo, &["add", "crates"]);
    git(
        repo,
        &["commit", "-q", "--no-verify", "-m", "monorepo crate"],
    );
    let monorepo_head = git(repo, &["rev-parse", "HEAD"]);
    let id = resolve(&env_of(&[]), &dropped, OsStr::new(GIT)).unwrap();
    assert_eq!(id.label(), format!("g{}.local", &monorepo_head[..12]));
    let id = resolve(&env_of(&[]), &vendored, OsStr::new(GIT)).unwrap();
    assert_eq!(id.label(), "unknown", "must not report the enclosing sha");
}

#[test]
fn fallback_with_uncommitted_change_is_never_unqualified() {
    let tmp = tempfile::tempdir().unwrap();
    let repo = tmp.path();
    init_repo(repo);
    let krate = copy_crate(&repo.join("crates/trust-ir"));
    git(repo, &["add", "crates"]);
    git(repo, &["commit", "-q", "--no-verify", "-m", "crate"]);
    let head = git(repo, &["rev-parse", "HEAD"]);

    // Own checkout, clean tree: the sha, but `.local` — the fallback cannot
    // attest the tree, so it never prints an unqualified `+g<sha>`.
    let id = resolve(&env_of(&[]), &krate, OsStr::new(GIT)).unwrap();
    assert_eq!(id.attestation, Attestation::Local);
    assert_eq!(id.sha.as_deref(), Some(head.as_str()));
    assert_eq!(id.label(), format!("g{}.local", &head[..12]));

    // Uncommitted change: still `.local`, never the unqualified label.
    fs::write(krate.join("build_identity.rs"), "// edited\n").unwrap();
    let directives = build_directives(&env_of(&[]), &krate, OsStr::new(GIT)).unwrap();
    let source = rustc_env(&directives, OUT_SOURCE);
    assert_eq!(source, format!("g{}.local", &head[..12]));
    assert_ne!(source, format!("g{}", &head[..12]));
    assert_eq!(rustc_env(&directives, OUT_ATTESTATION), "local");

    // The fallback re-runs when HEAD moves.
    assert!(
        directives
            .iter()
            .any(|d| d.starts_with("cargo:rerun-if-changed=") && d.ends_with("HEAD")),
        "{directives:?}"
    );
}

/// The `rerun-if-changed` paths of `directives`, by file name.
fn watched(directives: &[String]) -> Vec<String> {
    directives
        .iter()
        .filter_map(|d| d.strip_prefix("cargo:rerun-if-changed="))
        .filter(|path| path.starts_with('/'))
        .map(|path| {
            Path::new(path)
                .file_name()
                .unwrap()
                .to_string_lossy()
                .into_owned()
        })
        .collect()
}

#[test]
fn a_detached_head_is_watched_alone_and_a_branch_through_its_refs() {
    let tmp = tempfile::tempdir().unwrap();
    let repo = tmp.path();
    init_repo(repo);
    let krate = copy_crate(&repo.join("crates/trust-ir"));
    git(repo, &["add", "crates"]);
    git(repo, &["commit", "-q", "--no-verify", "-m", "crate"]);
    git(repo, &["pack-refs", "--all"]);
    let branch = git(repo, &["symbolic-ref", "--short", "HEAD"]);

    // On a branch, HEAD is resolved through the ref, packed here: `packed-refs`
    // and the directory a commit writes the loose ref into are watched too.
    let directives = build_directives(&env_of(&[]), &krate, OsStr::new(GIT)).unwrap();
    let on_branch = watched(&directives);
    assert!(on_branch.contains(&"HEAD".to_owned()), "{directives:?}");
    assert!(
        on_branch.contains(&"packed-refs".to_owned()),
        "{directives:?}"
    );
    assert!(
        on_branch.contains(&"heads".to_owned()),
        "{directives:?} ({branch})"
    );

    // Detached (as a superproject's submodule always is), HEAD holds the commit
    // and is all git reads: refs packed by a fetch must not re-run the script.
    git(repo, &["checkout", "-q", "--detach"]);
    let directives = build_directives(&env_of(&[]), &krate, OsStr::new(GIT)).unwrap();
    assert_eq!(watched(&directives), ["HEAD"], "{directives:?}");
    let head = git(repo, &["rev-parse", "HEAD"]);
    assert_eq!(
        rustc_env(&directives, OUT_SOURCE),
        format!("g{}.local", &head[..12])
    );
}

#[test]
fn linked_packed_nested_branch_fast_forward_refreshes_compiled_stamp() {
    let tmp = tempfile::tempdir().unwrap();
    let repo = tmp.path().join("repository");
    let linked = tmp.path().join("linked");
    fs::create_dir(&repo).unwrap();
    init_repo(&repo);
    let krate = copy_crate(&repo.join("crates/trust-ir"));
    // A dependency-free probe executes the actual build script, not a copy
    // of its resolution rule. Its own checkout has the required crate path.
    fs::write(
        krate.join("Cargo.toml"),
        "[package]\nname = \"stamp-probe\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::create_dir(krate.join("src")).unwrap();
    fs::write(
        krate.join("src/main.rs"),
        "fn main() { println!(\"{}\", env!(\"TIR_BUILD_GIT_SHA\")); }\n",
    )
    .unwrap();
    fs::write(
        repo.join("rust-toolchain.toml"),
        "[toolchain]\nchannel = \"trust\"\n",
    )
    .unwrap();
    let cargo = std::env::var_os("CARGO").expect(
        "run cli_version through scripts/run-targo.sh so CARGO names the actual Trust tool",
    );
    let lock = Command::new(&cargo)
        .args(["generate-lockfile", "--offline", "--manifest-path"])
        .arg(krate.join("Cargo.toml"))
        .output()
        .unwrap();
    assert!(
        lock.status.success(),
        "{}",
        String::from_utf8_lossy(&lock.stderr)
    );
    git(&repo, &["add", "crates", "rust-toolchain.toml"]);
    git(&repo, &["commit", "-q", "--no-verify", "-m", "probe"]);
    let before = git(&repo, &["rev-parse", "HEAD"]);
    git(
        &repo,
        &[
            "worktree",
            "add",
            "-q",
            "-b",
            "agents/stamp/nested",
            linked.to_str().unwrap(),
            &before,
        ],
    );
    git(
        &repo,
        &["commit", "-q", "--no-verify", "--allow-empty", "-m", "next"],
    );
    let after = git(&repo, &["rev-parse", "HEAD"]);
    assert_ne!(before, after);
    git(&repo, &["pack-refs", "--all", "--prune"]);
    let branch_path = PathBuf::from(git(
        &linked,
        &["rev-parse", "--git-path", "refs/heads/agents/stamp/nested"],
    ));
    assert!(!branch_path.exists());
    // Git versions differ in whether pack-refs removes empty directories.
    // Model the real packed-ref case where several parents do not exist.
    for parent in branch_path.ancestors().skip(1).take(2) {
        if parent.exists() {
            fs::remove_dir(parent).unwrap();
        }
    }
    assert!(!branch_path.parent().unwrap().exists());
    let head_path = PathBuf::from(git(&linked, &["rev-parse", "--git-path", "HEAD"]));
    let head_text = fs::read(&head_path).unwrap();
    let linked_crate = linked.join("crates/trust-ir");
    let files = [
        "Cargo.toml",
        "Cargo.lock",
        "build.rs",
        "build_identity.rs",
        "src/main.rs",
    ];
    let source_bytes: Vec<_> = files
        .iter()
        .map(|name| fs::read(linked_crate.join(name)).unwrap())
        .collect();
    let directives = build_directives(&env_of(&[]), &linked_crate, OsStr::new(GIT)).unwrap();
    let run = || {
        let out = Command::new(&cargo)
            .args([
                "--unverified",
                "run",
                "--quiet",
                "--offline",
                "--locked",
                "--manifest-path",
            ])
            .arg(linked_crate.join("Cargo.toml"))
            .env("CARGO_TARGET_DIR", tmp.path().join("target"))
            .env_remove(ENV_GIT_SHA)
            .env_remove(ENV_GIT_DIRTY)
            .env_remove("TRUST_BUILD_GIT_SHA")
            .env_remove("TRUST_BUILD_GIT_DIRTY")
            .output()
            .unwrap();
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8(out.stdout).unwrap().trim().to_string()
    };
    let first_stamp = run();
    git(&linked, &["merge", "--ff-only", &after]);
    assert_eq!(
        fs::read(&head_path).unwrap(),
        head_text,
        "symbolic HEAD text stays unchanged"
    );
    for (name, expected) in files.iter().zip(source_bytes) {
        assert_eq!(
            fs::read(linked_crate.join(name)).unwrap(),
            expected,
            "{name} was not edited"
        );
    }
    let second_stamp = run();
    println!(
        "linked packed nested ref: first={first_stamp}, second={second_stamp}, expected={after}"
    );
    assert_eq!(first_stamp, before);
    assert_eq!(
        second_stamp, after,
        "a Git-only fast-forward must rebuild the embedded stamp"
    );
    assert!(
        directives.iter().any(|line| {
            line.strip_prefix("cargo:rerun-if-changed=")
                .map(Path::new)
                .is_some_and(|path| path != branch_path && branch_path.starts_with(path))
        }),
        "the packed ref needs an existing watched ancestor: {directives:?}"
    );
}
