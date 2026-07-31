use std::path::{Path, PathBuf};
use std::process::Command;

fn rustc_version(rustc: &Path, private_dylib_dir: Option<&Path>) -> Option<String> {
    let mut command = Command::new(rustc);
    command
        .arg("--version")
        .env_remove("DYLD_LIBRARY_PATH")
        .env_remove("DYLD_FALLBACK_LIBRARY_PATH")
        .env_remove("LD_LIBRARY_PATH");
    if let Some(private) = private_dylib_dir {
        // Force the candidate driver ahead of the staged compiler's rpath. A
        // rustc_driver filename hash can remain stable across source commits;
        // executing the shim with the candidate loaded is the reliable ABI and
        // source-version identity check.
        command.env("DYLD_LIBRARY_PATH", private).env("LD_LIBRARY_PATH", private);
    }
    let output = command.output().ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout).ok().map(|version| version.trim().to_string())
}

fn rustc_matches_linked_driver(rustc: &Path) -> bool {
    rustc_version(rustc, None)
        .zip(trust_ir_frontend::linked_rustc_version())
        .is_some_and(|(actual, expected)| actual.ends_with(expected))
}

/// Locate the ABI-matching stage1 toolchain root. The canonical private build
/// uses stage0, so a build-time `RUSTC` is accepted only after a version check.
pub fn find_stage1_root() -> Option<PathBuf> {
    if let Ok(rustc) = std::env::var("RUSTC") {
        if !rustc.is_empty() {
            let path = PathBuf::from(&rustc);
            if rustc_matches_linked_driver(&path) {
                if let Some(root) = path.parent().and_then(Path::parent) {
                    if private_dylib_dir(root).is_some() {
                        return Some(root.to_path_buf());
                    }
                }
            }
        }
    }

    // frontend -> trust-ir -> first-party -> trust checkout.
    let trust_root = Path::new(env!("CARGO_MANIFEST_DIR")).ancestors().nth(3)?;
    let mut matches = Vec::new();
    for entry in std::fs::read_dir(trust_root.join("build")).ok()?.flatten() {
        let candidate = entry.path().join("stage1");
        if rustc_matches_linked_driver(&candidate.join("bin/rustc"))
            && private_dylib_dir(&candidate).is_some()
        {
            let candidate = std::fs::canonicalize(&candidate).unwrap_or(candidate);
            if !matches.contains(&candidate) {
                matches.push(candidate);
            }
        }
    }
    (matches.len() == 1).then(|| matches.remove(0))
}

/// Locate a bootstrap-prepared rustc-driver dylib directory matching stage1.
///
/// Bootstrap keeps old private sysroots in this directory, and a
/// `librustc_driver` filename hash can remain unchanged across source commits.
/// Require the exact filename, then execute the staged rustc shim with each
/// candidate forced into its dynamic-loader path and retain only candidates
/// that report the staged compiler's exact version. This prevents an older
/// same-filename driver from being selected merely because its directory sorts
/// first.
pub fn private_dylib_dir(stage1: &Path) -> Option<PathBuf> {
    let host_build = stage1.parent()?;
    let host = host_build.file_name()?.to_str()?;
    let mut stage1_drivers: Vec<_> = std::fs::read_dir(stage1.join("lib"))
        .ok()?
        .flatten()
        .filter_map(|file| {
            let name = file.file_name();
            name.to_str()
                .is_some_and(|name| {
                    name.starts_with("librustc_driver-")
                        && (name.ends_with(".dylib") || name.ends_with(".so"))
                })
                .then_some(name)
        })
        .collect();
    stage1_drivers.sort();
    stage1_drivers.dedup();
    let driver = (stage1_drivers.len() == 1).then(|| stage1_drivers.remove(0))?;
    let stage1_rustc = stage1.join("bin/rustc");
    let stage1_version = rustc_version(&stage1_rustc, None)?;

    let roots = host_build.join("rustc-private-sysroots");
    let mut matches = Vec::new();
    for entry in std::fs::read_dir(roots).ok()?.flatten() {
        let candidate = entry.path().join(host);
        if candidate.join(&driver).is_file()
            && rustc_version(&stage1_rustc, Some(&candidate)).as_deref()
                == Some(stage1_version.as_str())
        {
            let candidate = std::fs::canonicalize(&candidate).unwrap_or(candidate);
            if !matches.contains(&candidate) {
                matches.push(candidate);
            }
        }
    }
    matches.sort();
    matches.into_iter().next()
}

pub fn private_dylib_dir_or_panic(stage1: &Path) -> PathBuf {
    private_dylib_dir(stage1)
        .expect("stage1 exists but its ABI-matching prepared rustc-private dylib directory is missing")
}

/// Build a rustc-driver command for artifact extraction tests.
///
/// Trust's stage1 compiler verifies by default. These tests exercise frontend
/// lowering and independently validate/interpret its TrustIR output; allowing
/// the compiler verifier to run first can reject a deliberately partial corpus
/// before our callback observes it. Make the artifact-only authority explicit
/// on the original command line (rather than having a callback mutate policy).
pub fn artifact_only_driver_command(bin: &str, stage1: &Path) -> Command {
    let rustc = stage1.join("bin/rustc");
    let private = private_dylib_dir_or_panic(stage1);
    let mut command = Command::new(bin);
    command
        .arg("-Zno-trust-verify")
        .env("RUSTC", rustc)
        .env("DYLD_LIBRARY_PATH", &private)
        .env("LD_LIBRARY_PATH", private)
        .env_remove("RUSTUP_TOOLCHAIN");
    command
}
