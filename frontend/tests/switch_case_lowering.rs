//! The `frontend/` MIR driver's switch cases, under a standing gate.
//!
//! A switch case is its selector's VALUE in its type's one spelling
//! (`docs/SPEC_RATIFICATIONS.md` §3.3). MIR's `SwitchInt` carries the `-1`
//! arm of an `i8` match as the bit pattern `255`, which the validator refuses
//! at an `i8` selector, so the MIR lowering sign-extends a signed selector's
//! cases and keeps an unsigned one's.
//!
//! WHY THIS IS ITS OWN TARGET. `frontend/` is excluded from the workspace, so
//! no workspace gate compiles it; this target is listed in the registry
//! `scripts/gates/frontend-lowering.frontend.tests`, which the standing gate
//! `frontend-lowering` runs (`scripts/ci_gates.sh`). It lived in
//! `real_lowering_acceptance.rs` until 2026-10-01, a target no standing gate
//! can run whole while four of its tests fail on pre-existing frontend drift
//! (CLAUDE.md, "Toolchain"); a registry line names a target, never a
//! test inside one, so the switch test moved rather than the gate growing a
//! name filter.
//!
//! TOOLCHAIN: as every real-lowering test, it spawns the built `trust_ir_mir`
//! driver under the ABI-matching Trust compiler (`support::trust_toolchain`),
//! and FAILS, never skips, when that compiler is unusable.

#![feature(rustc_private)]

use std::path::Path;

mod support;
use support::{artifact_only_driver_command, trust_toolchain};

/// The one function of `module` whose (mangled) name ends in `suffix`.
fn fn_ending_in<'m>(module: &'m trust_ir::Module, suffix: &str) -> &'m trust_ir::Function {
    let matches: Vec<_> =
        module.functions.iter().filter(|function| function.name.ends_with(suffix)).collect();
    assert_eq!(
        matches.len(),
        1,
        "[switch-case] expected exactly one function ending in {suffix:?}; got {:?}",
        matches.iter().map(|function| function.name.as_str()).collect::<Vec<_>>()
    );
    matches[0]
}

/// Each selector of `tests/fixtures/switch_case_corpus.rs`: its symbol, the
/// selector type the driver emits, the case values it must emit (the
/// selector's VALUES), and `(argument, result)` runs the interpreter must
/// reproduce. The driver lowers `isize` / `usize` to the fixed-width `i64` /
/// `u64` (`mir_lower.rs`, its host-only type map), so those two cells pin
/// that mapping and the sign extension at it: the `-1` arm of an `isize`
/// match arrives from MIR as `2^64 - 1` and must come out `-1`.
#[test]
fn mir_switch_cases_are_their_selectors_values() {
    let toolchain = trust_toolchain();

    let bin = env!("CARGO_BIN_EXE_trust_ir_mir");
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/switch_case_corpus.rs");
    let cells: [(&str, trust_ir::Ty, &[i128], &[(i128, i128)]); 5] = [
        (
            "signed_byte_match",
            trust_ir::Ty::I8,
            &[-1, -128, 5],
            &[(-1, 10), (-128, 20), (5, 30), (127, 0), (0, 0)],
        ),
        (
            "signed_word_match",
            trust_ir::Ty::I64,
            &[-1, i64::MIN as i128],
            &[(-1, 10), (i64::MIN as i128, 20), (i64::MAX as i128, 0)],
        ),
        (
            "unsigned_byte_match",
            trust_ir::Ty::U8,
            &[255, 0],
            &[(255, 10), (0, 20), (1, 0)],
        ),
        (
            "signed_pointer_match",
            trust_ir::Ty::I64,
            &[-1, i64::MIN as i128],
            &[(-1, 10), (i64::MIN as i128, 20), (1, 0)],
        ),
        (
            "unsigned_pointer_match",
            trust_ir::Ty::U64,
            &[u64::MAX as i128, 0],
            &[(u64::MAX as i128, 10), (0, 20), (1, 0)],
        ),
    ];
    for (symbol, selector, expected_cases, runs) in cells {
        let outpath = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{symbol}.tir"));
        let _ = std::fs::remove_file(&outpath);
        let mut cmd = artifact_only_driver_command(bin, &toolchain);
        cmd.arg("--mir-emit-closure");
        cmd.arg(symbol);
        cmd.arg(&outpath);
        cmd.arg("--crate-type=lib");
        cmd.arg(&corpus);

        let out = cmd.output().expect("failed to spawn trust_ir_mir");
        let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
        combined.push_str(&String::from_utf8_lossy(&out.stderr));
        assert!(
            out.status.success() && combined.contains("EMIT-CLOSURE-OK"),
            "[switch-case] {symbol} no longer lowers.\n---- full output ----\n{combined}"
        );
        assert!(
            combined.contains("validate_module = 0 error(s)"),
            "[switch-case] {symbol}: emitted module is not validation-clean.\n\
             ---- full output ----\n{combined}"
        );

        let text = std::fs::read_to_string(&outpath).unwrap_or_else(|error| {
            panic!("[switch-case] cannot read emitted module {}: {error}", outpath.display())
        });
        let module = trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|error| panic!("[switch-case] module does not parse: {error:?}"));
        let function = fn_ending_in(&module, symbol);
        let mut cases: Vec<i128> = function
            .instructions()
            .filter_map(|node| match &node.inst {
                trust_ir::Inst::Switch { cases, .. } => Some(cases),
                _ => None,
            })
            .flatten()
            .map(|case| match &case.value {
                trust_ir::Constant::Int(value) => *value,
                other => panic!("[switch-case] {symbol}: a non-Int case {other:?}\n{text}"),
            })
            .collect();
        cases.sort_unstable();
        let mut expected = expected_cases.to_vec();
        expected.sort_unstable();
        assert_eq!(
            cases, expected,
            "[switch-case] {symbol}: the cases are the selector's values.\n---- emitted ----\n{text}"
        );
        assert_eq!(
            module.func_type(function.ty).and_then(|sig| sig.params.first()),
            Some(&selector),
            "[switch-case] {symbol}: the selector type.\n---- emitted ----\n{text}"
        );

        for (arg, want) in runs {
            let arg = trust_ir::interpret::InterpretValue::int(selector.clone(), *arg)
                .expect("an in-range argument");
            let outcome = trust_ir::interpret::Interpreter::with_module(&module)
                .execute_func(function.id, vec![arg.clone()])
                .unwrap_or_else(|error| panic!("[switch-case] {symbol}: interpreter failed: {error:?}"));
            let got = outcome
                .returns
                .first()
                .and_then(|value| value.as_int())
                .map(|value| value.as_signed());
            assert_eq!(got, Some(*want), "[switch-case] {symbol}({arg:?}) interpreter parity");
        }
    }
}
