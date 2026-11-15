use std::path::{Path, PathBuf};
use std::process::Command;

/// The Trust compiler whose `rustc_driver` this frontend links.
///
/// The REAL-lowering and soundness gates spawn the built driver binaries, which
/// need that compiler's sysroot (standard library) and its `lib/` directory
/// (the `librustc_driver-*` dylib). The installed Trust sysroot ships both, so
/// `targo --unverified test --manifest-path frontend/Cargo.toml` is the whole
/// recipe; the x.py `build/<host>/stage1` + private-sysroot pair these tests
/// used to hunt for is no longer needed.
///
/// The driver still derives its own `--sysroot` from `RUSTC` (through
/// `append_matching_rustc_sysroot`, version-checked), so these gates exercise
/// that product path too.
pub struct TrustToolchain {
    pub rustc: PathBuf,
    /// `<sysroot>/lib`: holds the `librustc_driver-*` this frontend links.
    pub dylib_dir: PathBuf,
}

fn clean_command(rustc: &Path) -> Command {
    let mut command = Command::new(rustc);
    command
        .env_remove("DYLD_LIBRARY_PATH")
        .env_remove("DYLD_FALLBACK_LIBRARY_PATH")
        .env_remove("LD_LIBRARY_PATH");
    command
}

fn stdout_of(mut command: Command, what: &str) -> Result<String, String> {
    let output = command
        .output()
        .map_err(|error| format!("could not run {what}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "{what} failed with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout).map_err(|_| format!("{what} printed non-UTF-8 output"))
}

fn resolve() -> Result<TrustToolchain, String> {
    // targo exports RUSTC to build scripts, not to test processes, so the
    // ordinary case is the `trustc` on PATH. Never a bare `rustc`.
    let rustc = std::env::var_os("RUSTC")
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("trustc"));
    let label = rustc.display().to_string();

    let mut version = clean_command(&rustc);
    version.arg("--version");
    let version = stdout_of(version, &format!("`{label} --version`"))?;
    let linked = trust_ir_frontend::linked_rustc_version()
        .ok_or("this frontend reports no linked rustc version")?;
    if !trust_ir_frontend::version_line_matches(&version, linked) {
        return Err(format!(
            "`{label}` is `{}`, but this frontend links rustc {linked}",
            version.trim()
        ));
    }

    let mut sysroot = clean_command(&rustc);
    sysroot.arg("--print=sysroot");
    let sysroot = PathBuf::from(stdout_of(sysroot, &format!("`{label} --print=sysroot`"))?.trim());
    let dylib_dir = sysroot.join("lib");
    let has_driver = std::fs::read_dir(&dylib_dir)
        .map_err(|error| format!("cannot read {}: {error}", dylib_dir.display()))?
        .flatten()
        .any(|entry| {
            entry
                .file_name()
                .to_str()
                .is_some_and(|name| name.starts_with("librustc_driver-"))
        });
    if !has_driver {
        return Err(format!(
            "{} holds no librustc_driver-* dylib",
            dylib_dir.display()
        ));
    }
    Ok(TrustToolchain { rustc, dylib_dir })
}

/// Resolve the linked Trust compiler, or FAIL the calling test.
///
/// These are the REAL-lowering and fail-loud SOUNDNESS gates. They used to
/// print `SKIP` and return (a PASS) whenever their x.py stage1 tree was absent
/// — which, on the installed Trust toolchain, was always, so every one of them
/// reported green over nothing. A gate that cannot run now fails and says why.
pub fn trust_toolchain() -> TrustToolchain {
    resolve().unwrap_or_else(|why| {
        panic!(
            "the rustc_private frontend gates need the Trust compiler this frontend links, \
             and it is not usable: {why}. Run them with `targo --unverified test \
             --manifest-path frontend/Cargo.toml` with `trustc` on PATH (or RUSTC=<that \
             trustc>). They fail rather than skip: a skipped soundness gate is a green \
             over nothing."
        )
    })
}

/// Build a rustc-driver command for artifact extraction tests.
///
/// Trust's compiler verifies by default (`-Ztrust-verify=on`, policy `strict`).
/// These tests exercise frontend lowering and independently validate/interpret
/// its TrustIR output; allowing the compiler verifier to run first can reject a
/// deliberately partial corpus before our callback observes it. Make the
/// artifact-only authority explicit on the original command line (rather than
/// having a callback mutate policy).
///
/// SCOPED NON-VERIFICATION LANE — `-Ztrust-verify=off` is deliberate here, not
/// a silenced failure. Two reasons, both about the subject under test:
///   1. The corpora are deliberately partial (that is what an extraction test
///      feeds), so a verification verdict over them carries no information.
///   2. This driver is an OUT-OF-TREE reimplementation of THIR -> TrustIR.
///      With verification on, the compiler runs its own in-tree `trust-ir`
///      lowering and may install derived MIR at the flip seam (see
///      `-Ztrust-ir-lower`: "batteries-on verification always runs it, so an
///      explicit value only takes effect in the `-Ztrust-verify=off`
///      compatibility lane"). That mutates the very MIR this driver extracts,
///      so leaving verification on would measure the in-tree lowering, not ours.
///
/// `-Ztrust-policy=advisory` is NOT the right rung here: it would fix (1) but
/// not (2), and it buys solver time for a verdict nothing reads.
///
/// Spelling matters: the retired `-Zno-trust-verify` does not exist in the
/// Trust compiler and dies at flag-parse ("unknown unstable option").
pub fn artifact_only_driver_command(bin: &str, toolchain: &TrustToolchain) -> Command {
    let mut command = Command::new(bin);
    command
        .arg("-Ztrust-verify=off")
        .env("RUSTC", &toolchain.rustc)
        .env("DYLD_LIBRARY_PATH", &toolchain.dylib_dir)
        .env("LD_LIBRARY_PATH", &toolchain.dylib_dir)
        .env_remove("RUSTUP_TOOLCHAIN");
    command
}
