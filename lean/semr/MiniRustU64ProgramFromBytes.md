# Complete-byte scalar program construction

`MiniRustU64ProgramFromBytes.construct` is a total, fail-closed constructor over
the complete actual `SemR.decode` result. It requires an executable target, the
exact U64 Const/Add/Return profile and full64 literal/input bounds. The result
retains the decoded View and constructs the actual generated MiniRust Exit
program. No separate caller-selected callee, model program or successful run is
accepted. The C/unit Exit entry is an explicit model harness, not a claim about
a Rust compiler's process-entry lowering.

`Construction` relates those same bytes to the full decoded module, literal,
name/target view, exact constructed program and actual `SemR.start` Core.
`Correspondence` combines the actual three-step `runBlob` result with the
existing complete generated-machine `ExitObservation`. `Available` constructs
the actual normal-stop oracle endpoint separately, preventing rejected choices
from making the all-branches statement vacuous. The proof composes the existing
real `Machine.new`, StorageLive, Call, callee steps/return and supported Exit;
all allocation guards, schedule/error choices, logs and complete final machine
and world remain those of the published model. No successful-new/frame/call/run
or NoUB premise replaces execution. The generated well-formedness check is also
proved for the actual constructed program.

Generic refusal laws retain decoder errors, unsupported target/shape and
out-of-range input. A closed range-decision proof is required by the host proof
factory; a host boolean is not authority. The original Returning program remains
unchanged and has its real UB endpoint. The separate Exit program still ends in
genuine MachineStop and retains its actual live caller/root Stack state.

The exact mathematical execution cut is
`5525be7f66db71509025ff62e89df4ef3277c829`, extending public
`c829513bf20f73fdaa691bd4869eb8ebe42375b1` with only two modules and additive
Lake roots. Narrow Lean checks pass. An initial namespace elaboration failure
is retained and contributes no accepted artifact. The independently source-built
maintained Clean reader is reused under exact named-executable custody:
`bedaa7dbf0a1cd8653537784ec70e7a87022c142413c99650620d7405489b0fb`;
adapter source `45537c9bb6fa3e8d98619088e43c2e73143f2e8725c7687112d0176e4200749b`,
kernel tree `69b9334b727f2973c39944c3a721f5035af5cc93`.

Its complete EMPTY-base logical type/body cone check covers **46 new targets,
7,714 constants and 6,810 units**, with 631 loaded modules and zero refusals.
Eight positive checks cover zero, eight with actual renamed input, max-u64,
current v63 input, semantic Sub refusal, input-range refusal, exact program
construction and a concrete full-machine endpoint. Four closed false goals
produce actual kernel TypeMismatch: wrong constructor, literal, world and stop.
No resource refusal counts as rejection. Existing equivalent decoder results
need not have equal bytes or distinct proof terms; subject custody is separate.

The independent result is retained under the producer's home directory at
`trust-scalar-source-model-20261107-umzh8b8v/qualification/reference-1/RESULT.json`,
SHA256 `f5cb82125579772fa215915a0d49e8ae865fda360e77baa0e74ec08d49a0b561`;
FULL SHA256 `88ae1a5e87790a6281b5d69678a930c508fec00a4435fbf78623a68dc68f8f27`.
All 9,335 inputs and recorded absences are unchanged at the check's bookends.
The mathematical provider stays immutable; documentation/publication uses a
separate source-only clone and preserves the qualified source bytes.

This is the concrete byte-to-whole-model construction prerequisite. Raw Rust,
THIR or Clean frontend Core to IR refinement, Rust codec/source correspondence,
physical ABI/ISA, SourceNoUB, body licence, proof grade and full G1–G8 remain
open. The captured-input host adapter must independently derive the complete
current byte subject and bind this separately identified mathematical extension;
neither an old producer fingerprint nor an old IR selector identifies it.
