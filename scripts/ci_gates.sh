#!/usr/bin/env bash
# Repo-side standing CI gate runner (Program CK1, trust-ir-side gates).
#
# Gates:
#   Every compiled test gate runs `targo test --workspace` (targo_test): one
#   feature resolution, so the dependency stack builds once for all of them.
#
#   1. lean-schema-parity   — the Rust<->Lean name-parity gate
#                             (--test lean_schema_parity).
#   2. workspace-build      — Targo build --locked over the workspace default
#                             members. (trust-ir-ay is deliberately NOT a
#                             default member: it carries the only external git
#                             dependency; gate 9 and ci-self-verify.sh test it.)
#   3. cli-gate-tests       — every trust-ir-cli test: the red/green
#                             integration coverage for `validate --lineage`
#                             (closed passes; Trusted rung and mis-threaded
#                             chains fail), `validate --forbid-trusted`
#                             (zero-Trusted passes; Trusted status/evidence
#                             each fail with the item named), and
#                             `validate --forbid-failed` (zero-Failed passes;
#                             a Failed obligation aborts with the item named).
#                             (The two thin tools shipped beside the CLI,
#                             trust-ir-diff and trust-ir-fmt, run their tests
#                             under gate 8's registry; see there.)
#   4. zero-trusted-census  — `validate --forbid-trusted` demonstrated against
#                             the conformance corpus: green on chc_batch.tmbc
#                             (no Trusted anywhere), red on
#                             proof_annotations.tmbc (10 Trusted obligation
#                             statuses + 1 Trusted evidence certificate — the
#                             census must FIRE and name them).
#   5. lineage-closure      — `validate --lineage` demonstrated red against
#                             chc_batch.tmbc with a current-schema empty sidecar
#                             (no rungs — fail-closed). The green half is gate
#                             3's cli_lineage (closed_lineage_passes,
#                             json_manifest_sidecar_accepted): binary and JSON
#                             sidecars carrying replay-authoritative evidence;
#                             a hand-written certless rung is never closed.
#   6. failed-obligation-census — `validate --forbid-failed` (the CK1 WS3-M1
#                             violated-contract build abort) demonstrated
#                             against the conformance corpus: green on
#                             chc_batch.tmbc (no Failed obligation), red on
#                             proof_diagnostics.tmbc (a Failed obligation with
#                             its refutation diagnostics — the census must
#                             FIRE and name it). The Failed rows in that
#                             fixture are also why the gate is a flag, not a
#                             default rejection.
#   7. dependency-pin-coherence — the Clean/AY pin is an atomic move
#                             (both manifests, the AY_REV provenance constant,
#                             the guard's own frozen constants,
#                             frontend/Cargo.lock, and the root Cargo.lock).
#                             The root lock now records both git authorities;
#                             the excluded frontend lock and source provenance
#                             constants still need this dedicated guard. The
#                             bumper separately checks the selected immutable
#                             Clean commit's seven co-owned AY declarations.
#                             Move a pin with scripts/bump-dep-pin.sh, never by hand.
#                             Gate 0 runs the toolchain-free mirror of every
#                             runtime assertion but one after its leg census
#                             (scripts/pin_rewrite.py static-guard); whether
#                             frontend/Cargo.lock resolves under --locked is
#                             Cargo's answer and is asked only here.
#                             Beside it, `import-verification` runs the
#                             import authenticator's own suite
#                             (--test verify_import; its round-trip row needs
#                             the `binary` feature, which the workspace enables):
#                             C1-C6 and R1-R7, including the WS8.14
#                             interposable-site refusal.
#   8. wire-format-goldens  — the conformance byte-goldens, i.e. the cross-repo
#                             contract tRust/TrustCg/ty/ay pin against.
#                             `coverage` fires when a new Ty/Inst/
#                             ProofAnnotation variant ships with no fixture in
#                             any of the four formats; `back_compat` holds the
#                             never-regenerated pinned blobs proving the
#                             MIN_READ_VERSION floor still reads;
#                             `sniff_format` holds the shared format-sniff
#                             table (trust_ir::codec) over the whole corpus.
#                             The registry also runs every test target of the
#                             two thin tools shipped beside the CLI (roadmap
#                             WS4.13 gate leg: no gate ran either before):
#                             trust-ir-diff (the semantic diff over all four
#                             formats, the crit.misw05 / scout-lean.A4 ports)
#                             and trust-ir-fmt (the canonical printer's shared
#                             format resolution, WS4.9).
#                             The native_request_bundle group is deliberately
#                             skipped — most of that crate's runtime for its
#                             least structural half; ci-self-verify.sh has it.
#                             Beside it, `wire-version-ledger` runs the
#                             binary wire-version reservation ledger
#                             (crates/trust-ir/wire_versions.tsv, roadmap
#                             WS8.5): VERSION is the highest shipped row,
#                             MIN_READ_VERSION the lowest readable one, every
#                             *_FORMAT_VERSION constant in binary.rs is named by
#                             its row (source scan), no literal read gate
#                             spells an unreserved number, each row agrees with
#                             the reader's real accept/refuse verdict, and
#                             reserved rows sit above VERSION. A number is reserved
#                             there BEFORE development writes it into a gate or
#                             golden — the v39/v42 collisions. It is an
#                             in-crate unit test (the constants are private,
#                             test -p trust-ir --features binary --lib, the
#                             same lib-test build as gate 10), so it cannot
#                             join a registry and runs as its own `gate` call.
#   9. validator-fail-closed — the closed validator holes (notably "Discharged
#                             obligation requires a ground certificate", the
#                             anti-faith-stamp rule).
#                             linked_import_authentication is the closure walk
#                             (validate_linked_module) over the same refusals.
#                             Also the workspace doctests (WS4.7): trust-ir's
#                             carry `compile_fail` type-level guards (e.g.
#                             `HashedModule`'s fields cannot be spelled outside
#                             the crate) that count only if something runs them.
#                             Beside it, `allocation-bounds` runs the
#                             allocation-size advisory's own suite
#                             (trust_ir::alloc_bound, `validate`'s advisory):
#                             its rules, element sizes on targets inside and
#                             outside the scalar-alignment table, a work
#                             census, every transfer function checked
#                             against the reference interpreter's integer
#                             arithmetic (exhaustively at 3 and 4 bits), and
#                             a differential against interpreter runs of
#                             random programs. In-crate unit tests (the
#                             transfer functions are private), run on the
#                             gate-10 lib-test build; each of the three test
#                             modules must be SEEN to run.
#                             Beside it too, `formula-dag` runs the registry
#                             of the hash-consed Formula DAG
#                             (trust_ir_contract::formula_dag): tree -> DAG
#                             -> tree is the identity for a witness of every
#                             variant (the list held complete by the serde
#                             derive) and for random shared formulas; an id
#                             of another DAG is refused; the let/define-fun
#                             printers expand to the tree text byte for byte
#                             and no binding is captured by a binder it is
#                             used under; ay proves each sharing text equal
#                             to its tree text; the per-node split of
#                             Formula::to_smtlib moved no byte; the
#                             printers' work counters double when the input
#                             does (wide, deep, shared and quantified
#                             inputs); and every walk is iterative on
#                             10^6-deep chains. Then the crate's own unit
#                             tests of the store (formula_dag::tests: every
#                             hash forced to collide, forged candidates, a
#                             shell filled with exactly its arity), which
#                             must be SEEN to run.
#  10. wire-allocation-census — `wire-allocations.toml` (repo root) is the
#                             allocation registry for the three contended
#                             counters on the wire: format versions, enum tag
#                             bytes, versioned identity strings (`<name>.vN`,
#                             `<name>-vN`: digest domains, schema tags). The
#                             census re-derives every row from the CODE — it
#                             runs the real writers and reads back the tag
#                             byte, probes the real reader with every version
#                             header, and scans the sources for constants and
#                             domain strings — so a version, tag or domain
#                             added without a row fails here, and a reserved
#                             row with no code behind it passes. The LIST of
#                             tag spaces the census samples is itself checked:
#                             binary.rs is scanned for every enum it matches to
#                             or from a literal tag byte (refusal arms, write
#                             arms, tag_enum! heads), so an unregistered wire
#                             enum fails. The gate also requires each live
#                             census test to be SEEN to pass: a name filter
#                             that matches nothing exits 0. Gate 0 runs the
#                             toolchain-free half (scripts/wire_alloc.py
#                             check); gate 8 carries the names-not-numbers lint.
#  11. two-language-ratchets — the ported 2026-09-17 two-language proof
#                             battery (roadmap WS8.6): every PASS row with its
#                             right-reason negative twin and every GAP ratchet
#                             in its exact recorded shape, each target checked
#                             as a bijection against
#                             crates/trust-ir-conformance/tests/two_language/
#                             RATCHETS.tsv, plus the harness's own mutation
#                             self-tests. Registry-backed:
#                             scripts/gates/two-language-ratchets.*.tests
#                             (the conformance targets and trust-ir-cli's
#                             two_language_cli, which gate 3 also runs). Green
#                             here does NOT mean the gaps are
#                             closed: a GAP row passes while the gap is present
#                             unchanged, and fails the moment it moves.
#  12. lean-exec-differential — the W5b Lean-EXECUTION differential oracle
#                             (roadmap WS2.19, closes the F-044 "no W5b
#                             oracle" row). The Lean executable semantics
#                             (`evalFunctionInContext`) is compiled into
#                             lean/trust_ir-semantics's `trustir_eval`
#                             executable (a serde-JSON module reader over the
#                             `TrustIr` library, built by the test itself via
#                             `lake build trustir_eval`), and the subset
#                             conformance fixtures plus the seeded W5a corpus
#                             run through BOTH it and the reference
#                             interpreter: any Ok/Ok value disagreement or
#                             Ok-vs-UB/panic/type-error disagreement fails;
#                             `unsupported` on either side is counted by
#                             feature and ratcheted (the count may not rise).
#                             Registry-backed (scripts/gates/
#                             lean-exec-differential.*.tests). REQUIRED
#                             (TRUST_IR_REQUIRE_LEAN=1) whenever
#                             $HOME/.elan/bin/lake exists; without a Lean
#                             toolchain the gate reports SKIP and the target's
#                             harness self-tests (the mutation control) still
#                             run.
#  13. verified-contracts   — THE VERIFIED LANE (scripts/verified_contracts.py).
#                             Every gate above compiles through `targo
#                             --unverified` and makes no proof claim; this one
#                             runs `targo trust check --release -p
#                             trust-ir-laws` with Trust's verification pass ON
#                             over the crate holding the laws of the pure
#                             decision tables (each a `pub fn` of
#                             crates/trust-ir-laws/src/laws.rs with an
#                             `ensures` contract): the validator's own tables
#                             there, and the tables resident in trust-ir the
#                             laws call across the crate boundary. It requires
#                             the strict gate green, EVERY law row `proved`
#                             with `Certified` / `KernelRechecked`
#                             (Clean-kernel re-checked), and each same-shape
#                             mutant of a table — a standalone copy (with a
#                             mutated trust-ir copy for a trust-ir table) run
#                             through the same lane — REFUTED on exactly the
#                             laws it breaks (the runner's `refuted
#                             obligation` line plus a non-zero exit; every
#                             untouched law of its scope still proved). Before
#                             any run, every law's body must be EXACTLY one
#                             call of its own table at the cell its name
#                             spells (WIRING): a batched mutant flips a law
#                             whichever table it calls; and every table over
#                             enum cells must have a law at every cell of its
#                             operand enums (a new variant or a deleted law
#                             is refused, not silently unproved).
#                             Every run must also be JUDGED (THE RULE in the
#                             script): peak RSS below the memory ceiling the
#                             report records, no budget stop, no unexplained
#                             published or omitted request — else it fails
#                             as `NOT JUDGED: <reason>`, because on the
#                             installed seal an RSS trip can PROVE a
#                             panicking function. And every run's build-
#                             script executions (THE BUILD-SCRIPT PREMISE in
#                             the script: its `build-execution-scope` rows,
#                             scripts run uncontained outside the proof
#                             channel, Trust blocker B5) must EQUAL scripts/
#                             gates/verified-contracts-build-scripts.tsv and
#                             are printed: each verdict rests on them.
#                             The verdict is about OPTIMIZED MIR (Trust guide
#                             §9h); the verdict lines are echoed verbatim. This
#                             is the opt-in lane CLAUDE.md's "Toolchain
#                             posture" asks for (the repo pin selects the
#                             Trust compiler; this gate makes the proof claim).
#  14. lean-proofs          — THE LEAN PROOFS (scripts/lean_proofs.py). Until
#                             2026-09-29 no gate ran `lake build` of
#                             lean/trust_ir-semantics (gate 12 builds only the
#                             `trustir_eval` executable), so every
#                             `(lean-theorem)` row and the AxiomAudit
#                             `#guard_msgs` printouts rested on a hand run.
#                             It runs `lake build TrustIr` (SDKROOT scrubbed,
#                             as gate 12) and fails on a build error (a stale
#                             `#guard_msgs` printout is one), on any
#                             "declaration uses 'sorry'" in the build log
#                             (Lake replays a cached module's log, so a warm
#                             build still shows it — the only check that sees
#                             one inside an `example`), then runs the
#                             whole-environment census
#                             lean/trust_ir-semantics/ProofCensus.lean: EVERY
#                             safe constant of a `TrustIr.*` module may rest
#                             on the Lean-core trio and `ay_sound_unsat` only
#                             (`Lean.ofReduceBool`, i.e. `native_decide`, only
#                             in the two executable-fixture modules), and the
#                             only safe `axiom` declared is `ay_sound_unsat`;
#                             refusals name the declaration and the axiom.
#                             The same run REPLAYS every one of those
#                             constants through the kernel
#                             (`Lean.Environment.replay`, lean4checker's
#                             engine, from `Init`): the census reads what the
#                             environment records, and a meta-program can
#                             record a constant the kernel never admitted (a
#                             planted `False` theorem passed the build and the
#                             census, measured 2026-09-29). A `native_decide`
#                             site is replayed with its evaluation re-run.
#                             Same kernel, second run: not an independent
#                             checker. Also refused: a `.lean` file under
#                             TrustIr/ that the root does not import (nothing
#                             would build it) and `debug.skipKernelTC` in the
#                             sources (a tripwire; the replay is the check).
#                             REQUIRED (--require) whenever
#                             $HOME/.elan/bin/lake exists, gate 12's
#                             condition; without it the gate prints SKIP,
#                             says no `(lean-theorem)` row is checked on this
#                             machine, and passes. Warm 9.5 s, cold 2 min 1 s
#                             (measured 2026-09-29).
#  15. verified-survey      — THE VERIFIED SURVEY (scripts/verified_survey.py),
#                             OPT-IN: it runs only with TRUST_IR_VERIFIED_SURVEY=1
#                             and otherwise prints SKIP and passes (still
#                             parsing its ledger), because a full survey took
#                             35-144 min and ~5 GiB of build tree plus up to
#                             1.2 GB of reports (measured 2026-09-29/30). It runs
#                             `targo trust check --allow-l0-gaps -p <crate>`
#                             (debug profile, the features the workspace
#                             resolves, CARGO_TARGET_DIR=target/verified-survey)
#                             over every workspace member, ignores targo's exit
#                             status, and reads each report per row. A crate is
#                             JUDGED only with no budget- or resource-
#                             attributable row, no budget stop in its output, a
#                             whole report stream and a peak RSS below the
#                             memory ceiling (gate 13's rule, from the same
#                             code); anything else is NOT JUDGED in both
#                             directions. For a judged crate every refutation
#                             (a `failed` row, or a native refutation the seal
#                             publishes as `unknown`: its verdict names
#                             `refuted obligation`, gate 13's evidence text)
#                             must be in scripts/gates/verified-survey-
#                             refutations.tsv (class verifier-false or policy;
#                             `true` is refused) — except a demoted law
#                             postcondition of gate 13's laws file, admitted
#                             on gate 13's verdict; a new refutation FAILS, and a
#                             ledgered one that is absent is "NOT JUDGED for that
#                             row", never a pass. Unknown and timeout rows are
#                             reported, never gated. Most crates are NOT JUDGED
#                             today: the gate is the instrument that turns green
#                             as Trust's deterministic budget lands, not a claim
#                             that any crate is verified. Gate 13 stays the
#                             --release contract lane.
#  16. verified-ready       — THE VERIFIED READY LANE (scripts/verified_ready.py),
#                             ON by default: the targets whose advisory run is
#                             already clean, from scripts/gates/verified-
#                             ready.tsv (today trust-ir-laws lib, trust-ir-fmt
#                             bins, trust-ir-diff bins). Per row it runs
#                             `targo trust check --allow-l0-gaps --locked -p
#                             <crate> --lib|--bins` (debug, CARGO_TARGET_DIR=
#                             target/verified-ready) and FAILS unless the run
#                             is JUDGED (gate 15's reader, gate 13's rule),
#                             the report's verification_gate has 0 failed and
#                             is not `fail`, the primary unit carries no
#                             refutation (a `failed` row or a demoted native
#                             one; no ledger), and its PROVED rows meet the
#                             row's floor. Unknown rows never count toward a
#                             floor. A PASS claims no target verified. About
#                             1-1.5 min (measured 2026-10-02, load 13-30).
#  17. frontend-lowering    — the test targets of the workspace-EXCLUDED
#                             `frontend/` package (the rustc_private MIR
#                             driver), which no gate above can compile: they
#                             run `test --locked --manifest-path
#                             frontend/Cargo.toml` (its own lock and feature
#                             resolution), through `run-targo.sh`, so
#                             unverified like every gate but 13 and 15.
#                             Registry-backed (scripts/gates/
#                             frontend-lowering.frontend.tests): a listed
#                             target must pass WHOLE, so a target with known
#                             failures stays off the list and a test that
#                             must be gated lives in a target that passes
#                             (the switch-case lowering, SPEC_RATIFICATIONS
#                             §3.3, moved out of real_lowering_acceptance for
#                             this). It needs the Trust compiler the frontend
#                             links (`trustc` on PATH, or RUSTC) and FAILS
#                             without it, as the targets themselves do.
#
# Gate 0 also carries `enforcement-links` (scripts/check_enforcement_links.py):
# every normative unit — a section of docs/SPEC_RATIFICATIONS.md, a numbered
# trusted-base item of TRUST.md — names what enforces it, with an evidence
# CLASS (kernel-certificate / lean-theorem / proved-contract / type-level /
# test / corpus / code / external / prose-only; a proved-contract entry cites
# a law gate 13 holds after a citation of the table it calls), and the gate resolves every
# citation against the tree: a cited test must be a real #[test] fn in a
# workspace crate, a cited file must exist, and the class must be WITNESSED
# by a citation of the matching kind, so rewording cannot raise one (a gate
# NAME or a fixture is a citation, never a witness; a feature witnesses type-level only if the
# manifest shows it off by default). The count of units with no
# checked evidence, and of ValidationError variants no test names or nothing
# constructs, is an append-only ledger (scripts/gates/enforcement-ratchet.txt)
# that goes down — except by a `correction` row, the recorded, reasoned
# downgrade of a unit that was overclassed; and a `not-normative` marker cannot
# retire a unit that was normative at the merge-base. It is the FIRST RUNG of moving
# in-text claims to mechanically verified proof: it proves no claim, it makes
# an unbacked or rotted one a gate failure. Toolchain-free, ~13 s.
#
# Gate 0 also carries `wire-allocation-owners` (scripts/wire_alloc.py owners),
# the one gate-0 step that asks the network: it lists origin's branches and
# FAILS when a lane deleted from origin still owns an open wire-allocation
# claim (the Single-enum claim named a deleted branch for three days with every
# gate green), or when a claim on origin's main names an unpinned lane that is
# no branch on origin or here (the roadmap runner's lanes commit straight to
# main), printing the `wire_alloc.py pin <lane>` that fixes it. Because
# its verdict follows origin, a commit that passed can fail it later, which is
# the point: the defect is the claim on main, fixed forward. Without the
# development history or a reachable origin it prints SKIP and passes.
#
# SELECTION, CACHE AND SCALE (scripts/gate_select.py, scripts/host_scale.py;
# docs/gates-inventory.md has the measurements). Before any gate runs, the
# planner maps the change (the diff from the merge-base with origin/main, or
# --base REV) through the real build graph — `targo metadata`, each target's
# module closure, the run-time reads its sources and doc comments spell
# (declared in scripts/gates/test-reads.tsv where they climb to the
# repository root), Lean imports, the registries — to the legs and test
# targets whose inputs it reaches, and prints the plan. Every other leg prints
# `SKIP (<reason>)`. A leg (or test target) whose COMPLETE input key already
# has a recorded PASS on this host is skipped as `cached PASS`; a PASS is
# recorded after it runs, while the tree, HEAD and origin/main still match the
# plan. FAIL-CLOSED: a build, toolchain, pin or gate input (any Cargo.toml or
# Cargo.lock, rust-toolchain*, .cargo/, build.rs, Lean package configuration,
# anything under scripts/), an unmapped path, an unreadable graph or diff,
# or `--all` (TRUST_IR_GATES=all) runs EVERY leg with no cache. With only a
# missing/changed green toolchain identity, every leg remains required but
# exact-input PASS records may be reused. FAIL invalidates older same-key PASS
# records; completion checks all required results and input bookends.
# A selected leg runs exactly the command it
# ran before; only WHETHER it runs, and which listed targets, is selected.
# Every Targo leg runs through host_scale.py, which reads cores, physical and
# available memory when the leg starts and sizes `-j` so that jobs x (the
# share one child of this leg took here) plus its heaviest child's excess fits
# the room it measured (available - margin), logs both, waits for room when
# not even one child fits, and refuses (COULD NOT RUN) only after the wait.
# TRUST_IR_TARGO_JOBS (and a positive CARGO_BUILD_JOBS) caps the job count.
#
# Usage: scripts/ci_gates.sh [--all] [--base REV]
#
# Non-zero exit on any gate failure. Cross-machine CI config remains a
# separate open item — this script is the honest repo-side runner.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PLAN_ARGS=()
while [[ $# -gt 0 ]]; do
    case "$1" in
        --all) PLAN_ARGS+=(--all) ;;
        --base)
            [[ $# -ge 2 ]] || { printf -- '--base needs a revision\n' >&2; exit 2; }
            PLAN_ARGS+=(--base "$2")
            shift
            ;;
        *) printf 'usage: scripts/ci_gates.sh [--all] [--base REV]\n' >&2; exit 2 ;;
    esac
    shift
done

FIXTURES="$ROOT/crates/trust-ir-conformance/tests/fixtures"
# Build parallelism: sized per leg by scripts/host_scale.py from the cores and
# the memory available when the leg starts; TRUST_IR_TARGO_JOBS caps it.
if [[ -n "${TRUST_IR_TARGO_JOBS:-}" ]]; then
    if [[ ! "$TRUST_IR_TARGO_JOBS" =~ ^[1-9][0-9]*$ ]]; then
        printf 'TRUST_IR_TARGO_JOBS must be a positive integer, got %q.\n' \
            "$TRUST_IR_TARGO_JOBS" >&2
        exit 2
    fi
fi
CURRENT_GATE=""
# targo_run <verb> <args...>: run-targo.sh through the host scaler, which adds
# `-j N` (N sized to the machine now) and records the leg's peak child RSS.
targo_run() {
    python3 -B "$ROOT/scripts/host_scale.py" run --leg "${CURRENT_GATE:-targo}" --jobs-flag -- \
        "$ROOT/scripts/run-targo.sh" "$@"
}
TARGO_RUNNER=targo_run

if [[ -n "${CARGO_TARGET_DIR:-}" ]]; then
    case "$CARGO_TARGET_DIR" in
        /*) TARGET_DIR="$CARGO_TARGET_DIR" ;;
        *) TARGET_DIR="$ROOT/$CARGO_TARGET_DIR" ;;
    esac
else
    TARGET_DIR="$ROOT/target"
fi
TRUST_IR_BIN="$TARGET_DIR/debug/trust-ir"

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

FAIL_COUNT=0
FAIL_NAMES=""
RUN_STARTED=$SECONDS

# --- The plan: which legs and targets this change reaches -------------------
PLAN="$TMP_DIR/plan.json"
RESULTS="$TMP_DIR/results.tsv"
: >"$RESULTS"
if ! python3 -B "$ROOT/scripts/gate_select.py" plan --root "$ROOT" \
    ${PLAN_ARGS[@]+"${PLAN_ARGS[@]}"} --out "$PLAN"; then
    printf 'gate plan FAILED: every leg runs, with no cache (fail closed)\n' >&2
    rm -f "$PLAN" "$PLAN.tsv"
fi
printf 'host: %s\n' "$(python3 -B "$ROOT/scripts/host_scale.py" measure 2>&1)"

# plan_lookup <leg>: PLAN_ACTION (run|skip), PLAN_REASON, PLAN_TARGETS (the
# selected test targets of a target-list leg; empty = the leg's whole list).
plan_lookup() {
    PLAN_ACTION=run
    PLAN_REASON="no plan: every leg runs"
    PLAN_TARGETS=""
    [[ -f "$PLAN.tsv" ]] || return 0
    local line
    line="$(awk -F'\t' -v u="$1" '$1 == u { print; exit }' "$PLAN.tsv")"
    if [[ -z "$line" ]]; then
        PLAN_REASON="not in the plan: runs"
        return 0
    fi
    IFS=$'\t' read -r _ PLAN_ACTION PLAN_REASON PLAN_TARGETS <<<"$line"
}
plan_runs() {
    plan_lookup "$1"
    [[ "$PLAN_ACTION" == run ]]
}
# in_plan_targets <name>: whether a test target is selected (true when the
# plan names no subset).
in_plan_targets() {
    [[ -z "$PLAN_TARGETS" ]] && return 0
    local t
    for t in $PLAN_TARGETS; do
        [[ "$t" == "$1" ]] && return 0
    done
    return 1
}

log() {
    printf '\n==> %s\n' "$*"
}

# targo_test <args...>: every compiled test gate selects the WHOLE workspace,
# so one feature resolution serves them all and trust-ir, trust-ir-build and
# the Clean/AY stack compile once. A per-crate `-p` selection resolves its own
# feature set: the gates used to rebuild that stack for each of six sets, and
# a `-p trust-ir` run compiled the `#![cfg(all(feature = ...))]` targets it
# named (make_aggregate_formats, array_splat_formats) to nothing.
targo_test() {
    "$TARGO_RUNNER" test --locked --workspace "$@"
}

# Registry-backed gates: the test targets live in scripts/gates/<gate>.<crate>.tests,
# one per line ('#' comments), merged with `merge=union` (.gitattributes) so that
# concurrent additions never conflict. Add a test there, not here.
# registry_args <file>: sets TEST_ARGS to (--test a --test b ...).
registry_args() {
    TEST_ARGS=()
    local line
    while IFS= read -r line || [[ -n "$line" ]]; do
        line="${line%%#*}"
        line="${line//[[:space:]]/}"
        [[ -n "$line" ]] && TEST_ARGS+=(--test "$line")
    done < "$1"
}
# run_registry <gate-name> [-- extra test args]: ONE workspace test run over the
# targets of every scripts/gates/<gate-name>.*.tests file that the plan
# selected (all of them without a plan). (Test target names are
# workspace-wide: a name two crates share runs in both.)
run_registry() {
    local gate_name="$1" f found=0 i
    local all=()
    shift
    for f in "$ROOT"/scripts/gates/"$gate_name".*.tests; do
        [[ -f "$f" ]] || continue
        found=1
        registry_args "$f"
        if [[ ${#TEST_ARGS[@]} -eq 0 ]]; then
            printf 'registry %s lists no tests\n' "$f" >&2
            return 1
        fi
        for ((i = 1; i < ${#TEST_ARGS[@]}; i += 2)); do
            in_plan_targets "${TEST_ARGS[$i]}" && all+=(--test "${TEST_ARGS[$i]}")
        done
    done
    if [[ $found -eq 0 ]]; then
        printf 'no registry scripts/gates/%s.*.tests\n' "$gate_name" >&2
        return 1
    fi
    if [[ ${#all[@]} -eq 0 ]]; then
        printf 'the plan selected no target of %s that its registry lists\n' "$gate_name" >&2
        return 1
    fi
    targo_test "${all[@]}" ${1+"$@"}
}

# run_excluded_registry <gate-name> <package-dir>: ONE test run over the
# targets of scripts/gates/<gate-name>.<package-dir>.tests, inside the
# workspace-EXCLUDED package <package-dir>/ — its own Cargo.lock and feature
# resolution, so `--manifest-path`, never `--workspace`.
run_excluded_registry() {
    local gate_name="$1" package="$2"
    local f="$ROOT/scripts/gates/$gate_name.$package.tests"
    if [[ ! -f "$f" ]]; then
        printf 'no registry %s\n' "$f" >&2
        return 1
    fi
    registry_args "$f"
    if [[ ${#TEST_ARGS[@]} -eq 0 ]]; then
        printf 'registry %s lists no tests\n' "$f" >&2
        return 1
    fi
    local selected=() i
    for ((i = 1; i < ${#TEST_ARGS[@]}; i += 2)); do
        in_plan_targets "${TEST_ARGS[$i]}" && selected+=(--test "${TEST_ARGS[$i]}")
    done
    if [[ ${#selected[@]} -eq 0 ]]; then
        printf 'the plan selected no target of %s that its registry lists\n' "$f" >&2
        return 1
    fi
    "$TARGO_RUNNER" test --locked --manifest-path "$ROOT/$package/Cargo.toml" "${selected[@]}"
}

# crate_tests <crate> <bin>: every test of one crate (the unit tests of its
# binary and every integration target under its tests/), run inside the
# workspace feature resolution rather than as `test -p <crate>`.
crate_tests() {
    local crate="$1" bin="$2" f name
    local args=()
    for f in "$ROOT/crates/$crate"/tests/*.rs "$ROOT/crates/$crate"/tests/*/main.rs; do
        [[ -f "$f" ]] || continue
        if [[ "${f##*/}" == main.rs ]]; then
            name="${f%/main.rs}"
            name="${name##*/}"
        else
            name="${f##*/}"
            name="${name%.rs}"
        fi
        in_plan_targets "$name" && args+=(--test "$name")
    done
    in_plan_targets "bin:$bin" && args=(--bin "$bin" ${args[@]+"${args[@]}"})
    if [[ ${#args[@]} -eq 0 ]]; then
        printf 'the plan selected no target of %s\n' "$crate" >&2
        return 1
    fi
    targo_test "${args[@]}"
}

# gate <name> <command...> — consult the plan; run the command, print
# PASS/FAIL, record failure; record a PASS under the leg's input key.
gate() {
    local name="$1" started
    shift
    plan_lookup "$name"
    if [[ "$PLAN_ACTION" != run ]]; then
        printf '\n==> gate %s: SKIP (%s)\n' "$name" "$PLAN_REASON"
        printf '%s\tSKIP\t%s\t\n' "$name" "$PLAN_REASON" >>"$RESULTS"
        return 0
    fi
    CURRENT_GATE="$name"
    log "gate $name: $*${PLAN_TARGETS:+ [selected: $PLAN_TARGETS]}"
    started=$SECONDS
    if "$@"; then
        printf 'PASS: %s (%d s)\n' "$name" "$((SECONDS - started))"
        printf '%s\tPASS\t%s\t%d\n' "$name" "$PLAN_REASON" "$((SECONDS - started))" >>"$RESULTS"
        if [[ -f "$PLAN" ]]; then
            python3 -B "$ROOT/scripts/gate_select.py" record --plan "$PLAN" --unit "$name" ||
                printf 'note: the PASS of %s was not recorded in the cache\n' "$name" >&2
        fi
    else
        printf 'FAIL: %s (%d s)\n' "$name" "$((SECONDS - started))" >&2
        printf '%s\tFAIL\t%s\t%d\n' "$name" "$PLAN_REASON" "$((SECONDS - started))" >>"$RESULTS"
        if [[ -f "$PLAN" ]]; then
            python3 -B "$ROOT/scripts/gate_select.py" record --plan "$PLAN" --unit "$name" --result FAIL ||
                printf 'note: the failure of %s was not recorded in the cache\n' "$name" >&2
        fi
        FAIL_COUNT=$((FAIL_COUNT + 1))
        FAIL_NAMES="$FAIL_NAMES $name"
    fi
    CURRENT_GATE=""
}

# Gate 4 (red half): the census must FIRE on proof_annotations.tmbc, which
# carries real Trusted obligation statuses and one Trusted evidence
# certificate. That fixture also fails plain well-formedness (it is a
# serialization-coverage fixture), so a bare non-zero exit proves nothing —
# require the census's own diagnostic to be present.
forbid_trusted_red() {
    local out code
    out="$("$TRUST_IR_BIN" validate --forbid-trusted \
        "$FIXTURES/proof_annotations.tmbc" 2>&1)"
    code=$?
    if [[ $code -ne 0 ]] && grep -q 'trusted census failed' <<<"$out"; then
        grep 'trusted census failed' <<<"$out"
        return 0
    fi
    printf 'expected exit != 0 with "trusted census failed", got exit %d:\n%s\n' \
        "$code" "$out" >&2
    return 1
}

# Gate 6 (red half): the census must FIRE on proof_diagnostics.tmbc, which
# carries a real Failed obligation status plus its refutation diagnostics
# (the module itself is well-formed, so the exit code is attributable to the
# census alone — require its diagnostic all the same, like gate 4).
forbid_failed_red() {
    local out code
    out="$("$TRUST_IR_BIN" validate --forbid-failed \
        "$FIXTURES/proof_diagnostics.tmbc" 2>&1)"
    code=$?
    if [[ $code -ne 0 ]] && grep -q 'failed-obligation census failed' <<<"$out"; then
        grep 'failed-obligation census failed' <<<"$out"
        return 0
    fi
    printf 'expected exit != 0 with "failed-obligation census failed", got exit %d:\n%s\n' \
        "$code" "$out" >&2
    return 1
}

# Gate 5 (red half): an empty manifest has no rungs to walk — the closure
# check must fail closed, not vacuously pass.
lineage_red() {
    local manifest="$TMP_DIR/lineage-empty.json"
    printf '{ "schema_version": 2, "nodes": [], "roots": [] }\n' >"$manifest"
    local out code
    out="$("$TRUST_IR_BIN" validate --lineage "$manifest" \
        "$FIXTURES/chc_batch.tmbc" 2>&1)"
    code=$?
    if [[ $code -ne 0 ]] \
        && grep -q 'lineage check failed' <<<"$out" \
        && grep -q 'manifest has no rungs to walk' <<<"$out" \
        && ! grep -q 'unsupported proof lineage schema' <<<"$out"; then
        grep 'lineage check failed' <<<"$out" | head -2
        return 0
    fi
    printf 'expected exit != 0 with "lineage check failed", got exit %d:\n%s\n' \
        "$code" "$out" >&2
    return 1
}

# Gate 10: the census is selected by test NAME (it is a `--lib` unit-test
# module: it drives crate-private writers, so it cannot be a `--test` target,
# which cargo would refuse if missing). A name filter that matches NOTHING
# exits 0 — measured: with the one line `mod wire_census;` dropped from
# binary.rs (a plausible merge resolution in the most hand-merged file in the
# repo) the old gate printed "running 0 tests ... ok" and PASSED. So exit 0 is
# not enough: every live census test must be SEEN to have run and passed. The
# list is `wire_alloc.py required-census-tests`, and a scripts/tests case holds
# every name in it to a real `fn` in wire_census.rs. Gate 0's
# `wire_alloc.py check` refuses the dropped hook too, without a compiler.
wire_census_ran() {
    local out code name missing=0
    out="$("$TARGO_RUNNER" test --locked -p trust-ir --features binary --lib \
        binary::wire_census 2>&1)"
    code=$?
    printf '%s\n' "$out"
    if [[ $code -ne 0 ]]; then
        return 1
    fi
    while IFS= read -r name; do
        [[ -n "$name" ]] || continue
        if ! grep -qE "^test binary::wire_census::${name} \.\.\. ok\$" <<<"$out"; then
            printf 'census test did not run: binary::wire_census::%s\n' "$name" >&2
            missing=1
        fi
    done < <(python3 -B "$ROOT/scripts/wire_alloc.py" required-census-tests)
    if [[ $missing -ne 0 ]]; then
        printf 'the wire census is not running — is `mod wire_census;` still in binary.rs?\n' >&2
        return 1
    fi
    grep -qE '^test result: ok\. [1-9][0-9]* passed; 0 failed' <<<"$out"
}

# lib_filter_ran <filter> [cargo args]: a name-filtered `--lib` run of trust-ir
# that must execute at least ONE test. No list of names to keep in step with
# somebody else's module: just not zero.
lib_filter_ran() {
    local filter="$1" out code
    shift
    out="$("$TARGO_RUNNER" test --locked -p trust-ir ${1+"$@"} --lib "$filter" 2>&1)"
    code=$?
    printf '%s\n' "$out"
    if [[ $code -ne 0 ]]; then
        return 1
    fi
    if ! grep -qE '^test result: ok\. [1-9][0-9]* passed; 0 failed' <<<"$out"; then
        printf 'the `%s` filter ran NO tests: the gate would have passed over nothing\n' \
            "$filter" >&2
        return 1
    fi
}

# Gate 0: the toolchain-free census of every Clean and AY pin leg followed by
# the exact static mirror of Gate 7's runtime assertions. Gate 7 remains the
# independent compiled parity check. Gate 0 also names the disagreeing file,
# which the lock-mismatch error from `clippy --locked` does not.
# Gate 0: the owners audit asks origin (`wire_alloc.py owners` exits 2 when it
# cannot: no development history, or origin unreachable). That is a printed
# SKIP, never a pass claim; a lane deleted from origin while it owns an open
# claim, or an unpinned claim on origin's main under a lane no branch carries,
# is a FAIL.
wire_owners_audit() {
    local code
    python3 -B "$ROOT/scripts/wire_alloc.py" --root "$ROOT" owners
    code=$?
    if [[ $code -eq 2 ]]; then
        printf 'SKIP: the wire-allocation owners audit judged nothing here (no development history, or origin could not be asked)\n'
        return 0
    fi
    return "$code"
}

# Gate 0: the object budget (scripts/check_object_budget.py) judges every
# commit origin/main..HEAD would push, not the tip tree: an archive added and
# deleted inside the range is still uploaded and kept by every clone. Its
# verdict follows the range, which no tree diff shows, so it runs on every
# plan. scripts/hooks/pre-push runs the same check at push time. Without
# origin/main there is no range to judge: a printed SKIP, never a pass claim.
# Only the checker's own NOT JUDGED (exit 3 with its marker) is that SKIP; any
# other non-zero exit fails, so a missing or renamed checker (Python exits 2)
# or a usage error never reads as green.
object_budget() {
    local out code
    out="$(python3 -B "$ROOT/scripts/check_object_budget.py" --root "$ROOT" --range origin/main..HEAD 2>&1)"
    code=$?
    printf '%s\n' "$out"
    if [[ $code -eq 3 ]] && grep -q '^OBJECT-BUDGET NOT JUDGED: ' <<<"$out"; then
        printf 'SKIP: the object budget judged nothing here (origin/main does not resolve)\n'
        return 0
    fi
    [[ $code -eq 0 ]] || return 1
}

pin_census() {
    local dep
    local status=0
    for dep in clean ay; do
        python3 -B "$ROOT/scripts/pin_rewrite.py" census --root "$ROOT" \
            --dep "$dep" || status=1
    done
    if [[ $status -ne 0 ]]; then
        printf 'Repair with: scripts/bump-dep-pin.sh <clean|ay> <40-hex-sha>\n' >&2
    fi
    if ! python3 -B "$ROOT/scripts/pin_rewrite.py" static-guard --root "$ROOT"; then
        status=1
    fi
    return "$status"
}

# --- Gate 0: repository policy and gate-tool regressions --------------------
gate zero-ignored-rust \
    python3 -B "$ROOT/scripts/check_no_ignored_rust.py" --root "$ROOT"
gate trust-default-authority \
    python3 -B "$ROOT/scripts/check_trust_default_authority.py" --root "$ROOT"
gate object-budget object_budget
gate dependency-pin-census pin_census
gate wire-allocation-registry \
    python3 -B "$ROOT/scripts/wire_alloc.py" --root "$ROOT" check
gate wire-allocation-owners wire_owners_audit
gate enforcement-links \
    python3 -B "$ROOT/scripts/check_enforcement_links.py" --root "$ROOT" check
gate internal-gate-tests bash "$ROOT/scripts/run_script_tests.sh"
format_workspace() (
    # Formatting has its own managed product; preserve the caller's build
    # target for later compilation while selecting the formatter normally.
    unset CARGO_TARGET_DIR
    "$ROOT/scripts/run-targo.sh" fmt --check --all
)
gate workspace-format format_workspace
# Tippy keeps its OWN target directory: Tippy and direct compilation record
# different compiler hashes, and one shared directory makes each overwrite the
# other's build-script fingerprints, rebuilding unchanged dependencies on every
# switch (CLAUDE.md, "Build, test, gates"). Keep it a sibling: putting a
# separate product inside an unclaimed build root prevents normal ownership
# admission when the workspace build starts.
lint() {
    CARGO_TARGET_DIR="$TARGET_DIR-tippy" "$TARGO_RUNNER" tippy --locked --workspace \
        --all-targets --all-features -- -D warnings
}
gate workspace-clippy lint

# --- Gate 1: the Rust<->Lean schema parity gate -----------------------------
gate lean-schema-parity targo_test --test lean_schema_parity

# --- Gate 2: the workspace build (default members) --------------------------
gate workspace-build "$TARGO_RUNNER" build --locked

# A workspace build unifies request-reexports through other members, hiding
# imports that break standalone consumers such as Clean's crystal projector.
# Check both the core API and that consumer's binary/formatter feature set.
# Compile unit tests separately too: normal `check --lib` omits cfg(test).
minimal_feature_build() {
    "$TARGO_RUNNER" check --locked -p trust-ir --lib --no-default-features &&
        "$TARGO_RUNNER" check --locked -p trust-ir --lib --no-default-features \
            --features binary,fmt &&
        "$TARGO_RUNNER" test --locked -p trust-ir --lib --no-default-features --no-run
}
gate minimal-feature-build minimal_feature_build

# --- Gate 3: every trust-ir-cli test (incl. gate 5's green half) ------------
# (Its tests run the binary their own test build produces, not gate 2's.)
gate cli-gate-tests crate_tests trust-ir-cli trust-ir

# Gates 4-6 run the trust-ir binary gate 2 built (the planner runs gate 2
# whenever one of them is selected, so the binary is this tree's).
binary_legs_selected() {
    local leg
    for leg in zero-trusted-census-green zero-trusted-census-red lineage-closure-red \
        failed-obligation-census-green failed-obligation-census-red; do
        plan_runs "$leg" && return 0
    done
    return 1
}
if binary_legs_selected && [[ ! -x "$TRUST_IR_BIN" ]]; then
    printf 'FAIL: %s missing — workspace build did not produce the CLI\n' \
        "$TRUST_IR_BIN" >&2
    FAIL_COUNT=$((FAIL_COUNT + 1))
    FAIL_NAMES="$FAIL_NAMES trust-ir-binary"
else
    # --- Gate 4: zero-Trusted census on the conformance corpus --------------
    gate zero-trusted-census-green \
        "$TRUST_IR_BIN" validate --forbid-trusted "$FIXTURES/chc_batch.tmbc"
    gate zero-trusted-census-red forbid_trusted_red

    # --- Gate 5: lineage closure against a sidecar manifest -----------------
    # The green half (closed_lineage_passes, json_manifest_sidecar_accepted in
    # trust-ir-cli's cli_lineage) runs in gate 3.
    gate lineage-closure-red lineage_red

    # --- Gate 6: zero-Failed census (violated-contract build abort) ---------
    gate failed-obligation-census-green \
        "$TRUST_IR_BIN" validate --forbid-failed "$FIXTURES/chc_batch.tmbc"
    gate failed-obligation-census-red forbid_failed_red
fi

# The remaining gates do not depend on the CLI binary, so they run
# unconditionally. Executing them last keeps gate numbering equal to execution
# order and puts their diagnostics immediately above the RESULT line.

# --- Gate 7: the Clean/AY dependency-pin coherence guard --------------------
gate dependency-pin-coherence targo_test --test dependency_pin_coherence
gate import-verification targo_test --test verify_import

# --- Gate 8: the conformance byte-goldens (cross-repo wire contract) --------
gate wire-format-goldens \
    run_registry wire-format-goldens -- --skip native_request_bundle

# Beside gate 8: the wire-version reservation ledger (in-crate unit test,
# so it cannot be a line in the trust-ir-conformance registry). It is selected
# by test NAME from a module gated on `feature = "binary"`, so — like gate 10 —
# it must be SEEN to run: drop the feature flag or the module and a bare
# `cargo test` reports `0 passed` and exits 0.
# The filter is the MODULE PATH: a bare `wire_version_ledger` also matches a
# census test whose name contains it, which kept this run non-empty — and so
# "seen to run" — with the ledger module compiled out (measured).
gate wire-version-ledger lib_filter_ran binary::wire_version_ledger:: --features binary

# --- Gate 9: validator fail-closed arms + the workspace doctests -------------
gate validator-fail-closed run_registry validator-fail-closed
gate trust-ir-doctests targo_test --doc

# Beside gate 9: the allocation-size advisory's suite (see the header). A
# dropped `#[path]` test module would leave the filter matching the others, so
# each module must be seen to pass a test, as gate 10's census tests are.
alloc_bound_ran() {
    local out code module
    out="$("$TARGO_RUNNER" test --locked -p trust-ir --features binary --lib alloc_bound:: 2>&1)"
    code=$?
    printf '%s\n' "$out"
    if [[ $code -ne 0 ]]; then
        return 1
    fi
    for module in tests property_tests differential_tests; do
        if ! grep -qE "^test alloc_bound::${module}::[a-z0-9_]+ \.\.\. ok\$" <<<"$out"; then
            printf 'no alloc_bound::%s test ran: is its module still declared in alloc_bound.rs?\n' \
                "$module" >&2
            return 1
        fi
    done
    grep -qE '^test result: ok\. [1-9][0-9]* passed; 0 failed' <<<"$out"
}
gate allocation-bounds alloc_bound_ran
# Beside gate 9: the FormulaDag suite (registry), then its in-crate unit
# tests, which only the crate can reach (they force every hash to collide).
formula_dag_ran() {
    local out code
    run_registry formula-dag || return 1
    out="$("$TARGO_RUNNER" test --locked -p trust-ir-contract --lib formula_dag:: 2>&1)"
    code=$?
    printf '%s\n' "$out"
    if [[ $code -ne 0 ]]; then
        return 1
    fi
    if ! grep -qE '^test formula_dag::tests::identity_is_exact_when_every_hash_collides \.\.\. ok$' <<<"$out"; then
        printf 'formula_dag::tests did not run: is its module still declared in formula_dag.rs?\n' >&2
        return 1
    fi
    grep -qE '^test result: ok\. [1-9][0-9]* passed; 0 failed' <<<"$out"
}
gate formula-dag formula_dag_ran

# --- Gate 10: the wire-allocation census (versions, tags, digest domains) ----
gate wire-allocation-census wire_census_ran

# --- Gate 11: the two-language ratchets (WS8.6) -----------------------------
gate two-language-ratchets run_registry two-language-ratchets

# --- Gate 12: the W5b Lean-execution differential oracle (WS2.19) -----------
# Required whenever the elan-installed lake exists (the harness locates it the
# same way: TRUST_IR_LAKE, then $HOME/.elan/bin/lake, then PATH). Elsewhere the
# registry still runs — the harness self-tests need no Lean — but a missing
# lake is a printed SKIP of the oracle runs, not a failure. The harness builds
# `trustir_eval` with SDKROOT REMOVED (`LAKE_SCRUBBED_ENV` in
# lean_exec_differential.rs): the elan toolchain links against its own bundled
# libc stubs, and Apple's xcrun shims (/usr/bin/git, /usr/bin/python3,
# /usr/bin/make) export SDKROOT into every child, so a gate launched through
# one of them used to fail the link on the macOS 26 SDK and pass without it.
lean_exec_differential() {
    if [[ -x "$HOME/.elan/bin/lake" ]]; then
        TRUST_IR_REQUIRE_LEAN=1 run_registry lean-exec-differential
    else
        printf 'no %s: the Lean-execution oracle runs are SKIPPED here (harness self-tests only)\n' \
            "$HOME/.elan/bin/lake"
        run_registry lean-exec-differential
    fi
}
gate lean-exec-differential lean_exec_differential

# --- Gate 13: the VERIFIED lane — proved contracts on the decision tables ----
# The only gate here with Trust's verification pass ON (every other gate runs
# `targo --unverified`). Per-row: every law of crates/trust-ir-laws proved and
# kernel-rechecked, every same-shape mutant refuted on exactly its laws. It
# resolves `targo trust` the way run-targo.sh does and never sets RUSTFLAGS.
gate verified-contracts \
    python3 -B "$ROOT/scripts/verified_contracts.py" --root "$ROOT"

# --- Gate 14: the Lean proofs — build, placeholders, whole-environment census -
# Required exactly where gate 12 is: whenever the elan-installed lake exists.
lean_proofs() {
    if [[ -x "$HOME/.elan/bin/lake" ]]; then
        python3 -B "$ROOT/scripts/lean_proofs.py" --root "$ROOT" --require
    else
        python3 -B "$ROOT/scripts/lean_proofs.py" --root "$ROOT"
    fi
}
gate lean-proofs lean_proofs

# --- Gate 15: the verified SURVEY — every workspace member, OPT-IN -----------
# 35-144 minutes and ~5 GiB + reports (measured 2026-09-29/30), so it runs only
# when asked. A PASS lists every NOT JUDGED crate: only JUDGED crates gate.
verified_survey() {
    if [[ "${TRUST_IR_VERIFIED_SURVEY:-}" == "1" ]]; then
        python3 -B "$ROOT/scripts/verified_survey.py" --root "$ROOT"
    else
        printf 'SKIP: the verified survey is opt-in (TRUST_IR_VERIFIED_SURVEY=1; 35-144 min, ~5 GiB + reports); '
        printf 'its ledger is still parsed and held to the tree:\n'
        python3 -B "$ROOT/scripts/verified_survey.py" --root "$ROOT" --check-ledger
    fi
}
gate verified-survey verified_survey

# --- Gate 16: the verified READY lane — clean targets held clean, proved floors -
# Additive to gates 13 and 15: it narrows nothing. Honors TRUST_IR_TARGO_JOBS.
verified_ready() {
    local rows=""
    [[ -n "$PLAN_TARGETS" ]] && rows="$(tr ' ' ',' <<<"$PLAN_TARGETS")"
    python3 -B "$ROOT/scripts/verified_ready.py" --root "$ROOT" ${rows:+--rows "$rows"}
}
gate verified-ready verified_ready

# --- Gate 17: the workspace-excluded frontend's gated test targets -----------
gate frontend-lowering run_excluded_registry frontend-lowering frontend

# --- Summary -----------------------------------------------------------------
if [[ -f "$PLAN" ]]; then
    if ! python3 -B "$ROOT/scripts/gate_select.py" finish --plan "$PLAN" --results "$RESULTS"; then
        printf 'FAIL: gate completion did not validate the results and input bookends\n' >&2
        FAIL_COUNT=$((FAIL_COUNT + 1))
        FAIL_NAMES="$FAIL_NAMES gate-completion"
    fi
fi
printf '\nlegs: %d ran (%d failed), %d skipped; wall %d s\n' \
    "$(awk -F'\t' '$2 != "SKIP"' "$RESULTS" | wc -l | tr -d ' ')" "$FAIL_COUNT" \
    "$(awk -F'\t' '$2 == "SKIP"' "$RESULTS" | wc -l | tr -d ' ')" "$((SECONDS - RUN_STARTED))"
if [[ $FAIL_COUNT -ne 0 ]]; then
    printf '\nRESULT: FAIL — %d gate(s):%s\n' "$FAIL_COUNT" "$FAIL_NAMES" >&2
    exit 1
fi
printf '\nRESULT: PASS — all gates green\n'
