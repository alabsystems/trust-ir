# Generic decoded scalar profile and actual MiniRust calls

`MiniRustU64ScalarCorrespondence.lean` composes the separately owned generic
canonical scalar profile with the existing actual generated-model full-function
proof. The historical 262-byte v38 subject remains a regression; the separately
retained 278-byte v63 subject is never called byte-identical to it.

`modelOfBytes` decodes the complete actual bytes, requires an executable target,
and classifies the exact one-function U64 Const/Add/Return shape. It constructs
the existing `MR_Function` from the classifier's actual literal. `ModelRelation`
retains the exact decoded view, including function name and all target fields;
the MiniRust function representation itself has no module/function-name or
TargetInfo field. This is an explicit bounded relation between the two models,
not a theorem that a Rust frontend or a compiler lowering produced MiniRust.

`enterFromBytes` passes that decoded callee to the unchanged real `eval_call`,
then invokes the unchanged real `Machine.step` twice. `profile_full_tree_exact`
keeps both guarded demonic allocations, argument initialization and stack push,
all scheduler choices/rejections, strict address/end/overlap guards, and the
complete resulting machine/world. `profile_function_correspondence` observes
`runBlob` on the same complete byte subject. No successful call, frame, run or
allowed branch is supplied as a premise. The existing eight-byte aligned caller
slot, full64 input/literal and explicit world boundary remain preconditions.

`profile_function_available` constructs actual fresh allocations from explicit
sufficient high-water room, independently of the safety theorem's rejected
branches. `exitState` preserves the real final step logs, caller result and
continuation, outside allocation records and both retired private allocations.
The existing scheduler resets prior accesses; no cumulative log is invented.

`MiniRustU64ScalarFixtures.lean` and `MiniRustU64ScalarControls.lean` instantiate
0,8,max-u64, renamed module/function, original v38 and current v63 inputs.
Closed complete-world controls include max-u64 wraparound. Hostile goals select
the wrong literal, semantic Sub, a wrong scalar and a world leaving the private
argument allocation live. They are judged by the maintained completion-sealed
Clean reference adapter, with real TypeMismatch required; a resource refusal
never counts as semantic rejection. Fixture byte provenance is in
`fixtures/generic-profile/MANIFEST.json`.

This work does not establish general source-to-MiniRust construction, codec or
frontend refinement, whole-program initialization/reachability, arbitrary
cross-model memory refinement, physical ABI/ISA, SourceNoUB, body licenses,
compiler grades or release completion. Generated MiniRust, SemR and its decoder
are unchanged. Imports are reused only over exact source bytes; logical type/body
cones must be independently checked at their exact retained source/artifact tuple.


### Exact generic-function qualification (2026-11-07)

The actual execution cut is `bbaffa7f95fe4a1c89eccefbac294ac3b184d3ff`, composed
losslessly from the Native full-call source and separately labelled generic
profile. Focused Lean checks cover the new correspondence and fixture modules.
The independent maintained Clean completion-sealed reference adapter checks the
new transitive logical type/body cone from EMPTY at local Clean
`e5e231015eb9fbc8648a7bcdecdec600ede39aaa`, kernel tree
`69b9334b727f2973c39944c3a721f5035af5cc93`: **75 new logical targets, 7,667
cone constants, 6,614 units, zero refusals**. Six closed complete-world positives
cover zero, eight, max-u64 wrapping, renamed module/function, original262B v38
and current278B v63. Four hostile claims produce actual kernel TypeMismatch:
wrong literal, semantic Sub, an argument allocation incorrectly left live, and a
wrong scalar. No resource refusal is counted as semantic rejection.

The exact maintained adapter source SHA256 is
`45537c9bb6fa3e8d98619088e43c2e73143f2e8725c7687112d0176e4200749b`.
The independent full result SHA256 is
`8cc15ebdec733fb9db129526c23c7098e7d5afbf2959d002daf61d7b1184b513`.
Source and complete selected input-population bookends are unchanged. Runtime,
parser and Rust kernel implementation remain TCB; this is not a proof of Rust
lowering, codec/frontend refinement, physical ABI, SourceNoUB, body license or
whole-compiler correctness. The explicit decoded-profile model construction is
checked; general frontend/source-to-MiniRust construction remains open.

Actual failed/refused attempts are retained: the initial alias-decider
elaboration error, and a pre-check Rust build failure caused by a source-cache
copy omitting legitimate `cc/src/target`. The latter is repaired using a separate
complete source home and runner, preserving all16,921 original failed input
hashes. No proof, module, grade, policy or resource limit was weakened. A doc or
merge successor reuses this result only while the mathematical/import inputs
remain byte-identical; the original execution cut is never relabelled.
