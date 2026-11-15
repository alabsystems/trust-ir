//! PRESERVED fail-loud REGRESSION gate for the frontend's soundness guards.
//!
//! Two HIGH silent-miscompiles of the "bare-name trait recognizer" class slipped
//! through earlier audits (`arith_binop_of` keyed off a method name; a user
//! method named `deref` mistaken for a pointer dereference). This integration
//! test locks the fail-loud guards in so they can NEVER silently regress: it
//! drives the REAL `trust_ir_frontend` lowering on `tests/fixtures/
//! negative_corpus.rs`, once per UNSOUND-shape fn (`--target-fn <name>`), and
//! asserts that EACH:
//!
//!   * prints a `LOWERING FAILED` line (the loud bail), AND
//!   * does NOT silently succeed (no `DIFFERENTIAL`/`ALL MATCH`/`emitted N
//!     block(s)` success marker, and the driver DID find the target fn).
//!
//! It also asserts a per-shape SUBSTRING of the bail message so a future
//! refactor that makes a fixture bail for the WRONG reason (masking that its
//! specific guard regressed) is caught. If any of these fixtures ever LOWERS
//! cleanly, a real soundness guard has regressed.
//!
//! TOOLCHAIN: like `real_lowering_acceptance.rs`, the lowering reads
//! `tcx.thir_body` via `rustc_private`, so it MUST run under the ABI-matching
//! Trust compiler (`RUSTC`, else `trustc` on PATH) with its sysroot's
//! `rustc_driver` (`support::trust_toolchain`). If that compiler is missing or
//! mismatched the test FAILS: it used to SKIP (and pass), which left this
//! soundness gate green over nothing on the installed toolchain.

#![feature(rustc_private)]

use std::path::Path;

mod support;
use support::{artifact_only_driver_command, trust_toolchain, TrustToolchain};

/// Run the built frontend binary on the NEGATIVE fixture with `--target-fn name`
/// under the linked Trust toolchain. Returns combined stdout+stderr.
fn run_target_fn(toolchain: &TrustToolchain, name: &str) -> String {
    let bin = env!("CARGO_BIN_EXE_trust_ir_frontend");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join("negative_corpus.rs");
    let mut cmd = artifact_only_driver_command(bin, toolchain);
    cmd.arg(&fixture);
    cmd.arg("--target-fn");
    cmd.arg(name);

    let out = cmd.output().expect("failed to spawn trust_ir_frontend");
    let mut combined = String::from_utf8_lossy(&out.stdout).into_owned();
    combined.push_str(&String::from_utf8_lossy(&out.stderr));
    combined
}

/// One unsound shape: the `--target-fn` name, a human label for the guard, and a
/// SUBSTRING the loud bail message must contain (so the RIGHT guard fired).
struct NegShape {
    target_fn: &'static str,
    guard: &'static str,
    bail_substr: &'static str,
}

/// The success markers the driver prints ONLY when a fn lowered cleanly. If ANY
/// appears for a fixture fn, a soundness guard has regressed (the unsound shape
/// silently lowered).
const SUCCESS_MARKERS: &[&str] = &["DIFFERENTIAL", "ALL MATCH", "emitted "];

#[test]
fn negative_corpus_every_unsound_shape_bails_loudly() {
    let toolchain = trust_toolchain();

    // One entry per UNSOUND shape. Each MUST bail with `LOWERING FAILED`, and the
    // bail message must contain `bail_substr` (the signature of its SPECIFIC
    // guard) — a fixture bailing for the WRONG reason would mask that its own
    // guard regressed.
    let shapes = [
        NegShape {
            target_fn: "neg_user_deref",
            guard: "is_deref_call (user inherent `deref` not peeled as a pointer deref)",
            // `lower_place` cannot model the user `deref()` Call scrutinee BECAUSE
            // the trait-identity guard refused to peel it (a bare-name recognizer
            // would have silently peeled it to the receiver).
            bail_substr: "unsupported scrutinee/arg place Call",
        },
        NegShape {
            // M5.7a made the COMMON one-level nested ctor (`Node(box Leaf, _)`)
            // supported; this case now guards the still-unsupported DEEPER nest
            // (`Node(box Node(box Leaf, _), _)`, a two-level nest whose inner ctor's
            // own fields are non-trivial), which must STILL bail loud.
            target_fn: "neg_nested_ctor",
            guard: "classify_arm_subpatterns (deeper-than-one-level nested constructor)",
            bail_substr: "nested/non-trivial subpattern in ADT-match arm",
        },
        NegShape {
            // M5.7f made enum-variant CONSTRUCTION supported (no-payload / Box-child
            // / inline-SCALAR variants), and M5.7e made aggregate-payload READING /
            // destructuring (`Span((a, b))`) supported — but CONSTRUCTING an
            // aggregate-payload variant (`Sym::Span((1, 2))`) is STILL deferred
            // (M5.7e covers the read side only; there is no aggregate-field Store).
            // `lower_enum_variant_construction` enters the construction path
            // (HeapAlloc + tag Store) but bails loud on the tuple field, the still-
            // unsupported construction-side aggregate case.
            target_fn: "neg_construct_variant",
            guard:
                "lower_enum_variant_construction (inline-aggregate payload CONSTRUCTION — deferred)",
            bail_substr: "an inline-aggregate (tuple/array/struct) payload has no",
        },
        NegShape {
            // M5.7e made a ONE-LEVEL aggregate destructure (`Span((a, b))`)
            // supported; this case now guards the still-unsupported NESTED aggregate
            // (`Deep(((a, b), c))`, an aggregate-in-aggregate). M5.7e walks only ONE
            // level of sub-field offsets (the bind path is `[outer_field, sub_field]`);
            // a deeper path reaches the dedicated depth guard and must STILL bail loud
            // (nested aggregate-in-aggregate is future work). (Name kept stable for
            // the regression harness; it now guards the NESTED aggregate.)
            target_fn: "neg_scalar_payload",
            guard: "aggregate-binding depth cap (nested aggregate-in-aggregate — M5.7e)",
            bail_substr: "nested aggregate-in-aggregate",
        },
        NegShape {
            target_fn: "neg_multi_deref",
            guard: "scalar-deref (multi-level `**rr`)",
            bail_substr: "multi-level scalar deref",
        },
        NegShape {
            // M6: the i32-tag guard is retired (the tag width is faithful now). The
            // surviving width guard caps the tag at a trust-ir Load width
            // (i8/i16/i32/i64); a `repr(i128)` enum has a 16-byte tag with no Load
            // width and must STILL bail loud.
            target_fn: "neg_wide_discr",
            guard: "tag-width cap (16-byte / i128-width tag has no trust-ir Load width)",
            bail_substr: "no matching trust-ir integer Load width",
        },
        NegShape {
            target_fn: "neg_toplevel_atbind",
            guard: "collect_bindings (top-level `x @ Pat` whole-value binding)",
            bail_substr: "top-level whole-value binding at the ADT-match scrutinee",
        },
    ];

    let mut bailed = 0usize;
    for shape in &shapes {
        let out = run_target_fn(&toolchain, shape.target_fn);

        // The driver MUST have found the target fn (else the test proves nothing).
        assert!(
            !out.contains("no target fn matched"),
            "[{}] driver did not find `{}` in the negative fixture — the test \
             would be vacuous.\n---- full output ----\n{out}",
            shape.guard,
            shape.target_fn
        );

        // 1) The loud bail MUST be present.
        assert!(
            out.contains("LOWERING FAILED"),
            "[{}] SOUNDNESS GUARD REGRESSED: `--target-fn {}` did NOT print \
             `LOWERING FAILED` — the unsound shape lowered without a loud bail.\n\
             ---- full output ----\n{out}",
            shape.guard,
            shape.target_fn
        );

        // 2) It MUST be the RIGHT guard (substring of the bail message).
        assert!(
            out.contains(shape.bail_substr),
            "[{}] `--target-fn {}` bailed, but NOT with the expected guard message \
             (missing substring {:?}) — it may be failing for an unrelated reason, \
             masking a regression of its OWN guard.\n---- full output ----\n{out}",
            shape.guard,
            shape.target_fn,
            shape.bail_substr
        );

        // 3) It MUST NOT have silently succeeded (no clean-lowering marker).
        for marker in SUCCESS_MARKERS {
            assert!(
                !out.contains(marker),
                "[{}] `--target-fn {}` printed a SUCCESS marker {:?} — the unsound \
                 shape silently lowered (a soundness guard regressed).\n\
                 ---- full output ----\n{out}",
                shape.guard,
                shape.target_fn,
                marker
            );
        }

        bailed += 1;
    }

    assert_eq!(
        bailed,
        shapes.len(),
        "expected all {} unsound shapes to bail loudly; only {bailed} did",
        shapes.len()
    );
    eprintln!(
        "negative_lowering: all {} unsound shapes bailed LOUDLY with their specific \
         guard message (fail-loud soundness guards intact).",
        shapes.len()
    );
}
