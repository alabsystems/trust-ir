// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Genuine generated entry for tests that run the compiler in process.
extern crate test;

/// Capture original scheduler custody before libtest reads arguments, opens
/// files or starts workers. The SDK retains its one-thread loan and refusals.
pub(super) fn native_test_main(tests: &[&test::TestDescAndFn]) {
    // SAFETY: generated main constructs only static test references before
    // this first native-entry operation, exactly as the SDK's driver tests do.
    if let Err(error) =
        unsafe { rustc_data_structures::jobserver::capture_early_for_test_harness() }
    {
        eprintln!("frontend test entry: inherited compiler scheduler refused: {error}");
        std::process::exit(75);
    }
    #[cfg(panic = "unwind")]
    let result = test::test_main_env_args(tests);
    #[cfg(not(panic = "unwind"))]
    let result = test::test_main_env_args_abort(tests);
    result.exit_process();
}
