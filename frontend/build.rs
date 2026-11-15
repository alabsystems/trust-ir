//! Build script for trust_ir_frontend.
//!
//! The driver binaries and the test harnesses link the compiler's
//! `librustc_driver-<hash>` dylib, which lives in `<sysroot>/lib` of the Trust
//! compiler building this crate. Nothing on a Trust machine puts that directory
//! on the loader path when a binary is started by hand or from a script (macOS
//! also strips `DYLD_*` whenever a command passes through `/bin/sh` or
//! `/usr/bin/env`), so without an rpath `target/*/trust_ir_mir` dies at load
//! with "no LC_RPATH's found". Bake one in, from the same compiler targo hands
//! this script as `RUSTC`.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=RUSTC");

    // Cargo/targo always set RUSTC for build scripts; `trustc` is the Trust
    // spelling, never a bare `rustc`.
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "trustc".to_string());
    let output = Command::new(&rustc)
        .args(["--print", "sysroot"])
        .output()
        .unwrap_or_else(|error| panic!("could not run {rustc} --print sysroot: {error}"));
    if !output.status.success() {
        panic!(
            "{rustc} --print sysroot failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let sysroot = PathBuf::from(
        String::from_utf8(output.stdout)
            .expect("UTF-8 sysroot")
            .trim(),
    );
    // Canonical, so the rpath names the concrete toolchain directory rather than
    // a link a later toolchain install could repoint under the same dylib name.
    let sysroot = sysroot.canonicalize().unwrap_or(sysroot);
    let lib = sysroot.join("lib");
    if !lib.is_dir() {
        panic!("compiler lib directory {} does not exist", lib.display());
    }
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib.display());
}
