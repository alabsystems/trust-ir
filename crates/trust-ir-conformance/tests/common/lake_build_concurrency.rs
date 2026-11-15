// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::sync::Barrier;

fn fake_lake(directory: &Path, script: &str) -> PathBuf {
    let lake = directory.join("lake");
    fs::write(&lake, format!("#!/bin/sh\nset -eu\n{script}")).unwrap();
    fs::set_permissions(&lake, fs::Permissions::from_mode(0o755)).unwrap();
    lake
}

#[test]
fn shared_package_builds_serialize_across_path_aliases() {
    let scratch = super::SemrScratch::new("lake-shared-builds");
    let package = scratch.path("package");
    fs::create_dir(&package).unwrap();
    let alias = scratch.path("alias");
    symlink(&package, &alias).unwrap();
    // An exclusive build output directory detects overlapping subprocesses,
    // even when the callers name the same package through different paths.
    let lake = fake_lake(
        &scratch.0,
        "if ! mkdir active; then\n  echo 'overlapping package writes' >&2\n  exit 73\nfi\ntrap 'rmdir active' EXIT\nsleep 0.1\n",
    );
    let start = Barrier::new(8);
    let outputs = std::thread::scope(|scope| {
        let builds: Vec<_> = (0..8)
            .map(|i| {
                let lake = &lake;
                let directory = if i % 2 == 0 { &package } else { &alias };
                let start = &start;
                scope.spawn(move || {
                    start.wait();
                    super::lake_build_command(lake, directory, "shared")
                        .output()
                        .unwrap()
                })
            })
            .collect();
        builds
            .into_iter()
            .map(|build| build.join().unwrap())
            .collect::<Vec<_>>()
    });
    for output in outputs {
        assert!(
            output.status.success(),
            "shared package build failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn independent_package_builds_can_overlap() {
    let scratch = super::SemrScratch::new("lake-independent-builds");
    let left = scratch.path("left");
    let right = scratch.path("right");
    fs::create_dir(&left).unwrap();
    fs::create_dir(&right).unwrap();
    // Both subprocesses must start before either can finish. A global lock
    // would time out here; separate package output trees may build together.
    let lake = fake_lake(
        &scratch.0,
        ": > ready\nremaining=200\nuntil [ -f ../left/ready ] && [ -f ../right/ready ]; do\n  remaining=$((remaining - 1))\n  if [ \"$remaining\" -eq 0 ]; then\n    echo 'independent package build was blocked' >&2\n    exit 74\n  fi\n  sleep 0.01\ndone\n",
    );
    std::thread::scope(|scope| {
        let builds: Vec<_> = [&left, &right]
            .into_iter()
            .map(|directory| {
                let lake = &lake;
                scope.spawn(move || {
                    super::lake_build_command(lake, directory, "independent")
                        .output()
                        .unwrap()
                })
            })
            .collect();
        for build in builds {
            let output = build.join().unwrap();
            assert!(
                output.status.success(),
                "independent package build failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    });
}

#[test]
fn lake_context_run_preserves_literal_program_arguments() {
    let scratch = super::SemrScratch::new("lake-context-args");
    let package = scratch.path("package");
    fs::create_dir(&package).unwrap();
    let lake = fake_lake(&scratch.0, "printf '%s\\n' \"$@\"\n");
    let output = super::lake_run_command(&lake, &package, "file with spaces.lean")
        .arg("--check-argv")
        .arg("two words")
        .arg("--literal")
        .arg("")
        .arg("--")
        .output()
        .unwrap();
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "lean\nfile with spaces.lean\n--\n--run\n--\n--check-argv\ntwo words\n--literal\n\n--\n"
    );
}

#[test]
fn lake_context_runs_and_builds_share_the_package_lock() {
    let scratch = super::SemrScratch::new("lake-context-shared");
    let package = scratch.path("package");
    fs::create_dir(&package).unwrap();
    let alias = scratch.path("alias");
    symlink(&package, &alias).unwrap();
    let lake = fake_lake(
        &scratch.0,
        "if ! mkdir active; then\n  echo 'overlapping build/context run' >&2\n  exit 73\nfi\ntrap 'rmdir active' EXIT\nsleep 0.1\n",
    );
    let start = Barrier::new(8);
    let outputs = std::thread::scope(|scope| {
        let runs: Vec<_> = (0..8)
            .map(|i| {
                let lake = &lake;
                let directory = if i % 2 == 0 { &package } else { &alias };
                let start = &start;
                scope.spawn(move || {
                    start.wait();
                    if i % 2 == 0 {
                        super::lake_build_command(lake, directory, "shared")
                            .output()
                            .unwrap()
                    } else {
                        super::lake_run_command(lake, directory, "Main.lean")
                            .output()
                            .unwrap()
                    }
                })
            })
            .collect();
        runs.into_iter()
            .map(|run| run.join().unwrap())
            .collect::<Vec<_>>()
    });
    for output in outputs {
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
