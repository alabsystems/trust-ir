import Lake
open Lake DSL

-- SemR (Trust proven-core RM4): trust-ir level R's semantics and binary
-- decoder (`SemR.lean`), MiniRust's generated operators (`MiniRust.lean`:
-- Trust's `scripts/trust_core/specr/SpecrPrelude.lean` and
-- `generated/MiniRustSlice.lean`, verbatim, in a `noncomputable section`),
-- the kernel lemmas equating SemR's operator layer with MiniRust's
-- (`SemRMiniRust.lean`), the memory slice's laws and its MiniRust byte
-- encoding (`SemRMemory.lean`), and the oracle executable the SemR differential
-- runs (`Main.lean`). Lean v4.30.0-rc2, the version Clean's reference entry
-- replays (`crates/clean-olean/tests/semr_reference.rs` in Clean).

package «semr» where

lean_lib SemR where
  roots := #[`SemR, `MiniRust, `SemRMiniRust, `SemRMemory]

lean_lib SemRStorage where

lean_lib ClosureConstruction where

lean_lib ClosureAxiomAudit where

lean_lib TensorContraction where

lean_lib PanicRelationCheck where

lean_lib U64AdditionReplay where

lean_lib U64AdditionAudit where

lean_lib U64Addition where

lean_lib MiniRustU64Function where

lean_lib MiniRustU64Execution where

lean_lib MiniRustU64Return where

lean_lib MiniRustU64Step where

lean_lib MiniRustU64Entry where

lean_lib MiniRustU64Call where

lean_lib MiniRustU64AllocatedCall where

lean_lib MiniRustAllocate8Safety where

lean_lib MiniRustAllocate where

lean_lib MiniRustAllocateCheck where

lean_lib MiniRustU64ProgramTyping where

lean_lib MiniRustU64ProgramDecode where

lean_lib MiniRustU64ProgramCheck where

lean_lib MiniRustMachineNew where

lean_lib MiniRustU64ProgramStart where

lean_lib MiniRustProgramStep where

lean_lib MiniRustU64ExitControls where

lean_lib MiniRustU64ExitExecution where

lean_lib MiniRustU64ExitStop where

lean_lib MiniRustU64ExitCall where

lean_lib MiniRustU64ExitRun where

lean_lib MiniRustU64ExitStart where

lean_lib MiniRustU64ExitProgram where

lean_lib MiniRustProgramExit where

lean_lib MiniRustProgramCall where

lean_lib MiniRustU64ProgramCall where

lean_lib MiniRustU64ProgramExecutionControls where

lean_lib MiniRustU64ProgramExecution where

lean_lib MiniRustU64ProgramReturn where

lean_lib MiniRustU64ProgramRun where

lean_lib MiniRustU64Program where

lean_lib MiniRustAllocate8Room where

lean_lib MiniRustAllocate8Audit where

lean_lib MiniRustU64Availability where

lean_lib MiniRustU64AvailabilityControls where

lean_lib U64ScalarProfile where

lean_lib MiniRustU64ScalarCorrespondence where

lean_lib MiniRustU64ScalarFixtures where

lean_lib MiniRustU64ScalarControls where

lean_lib MiniRustU64Replay where

lean_lib MiniRustU64RetainedClaims where

lean_lib MiniRustU64Run where

lean_lib MiniRustU64Correspondence where

lean_lib MiniRustU64Controls where

lean_lib MetadataCheck where

lean_lib SemREntry where

lean_lib SemREntryCheck where

lean_lib SemREntryAxiomAudit where

lean_lib SemREntryBody where

lean_lib SemREntryBodyCheck where

lean_lib SemREntryBodyAxiomAudit where

lean_lib SemRSourceBodyCheck where

lean_lib SemRSourceBodyAxiomAudit where

lean_lib SemRRuntimeMain where

@[default_target]
lean_exe semr_eval where
  root := `Main

-- Runtime controls mutate SemR while the production target retains all audits.
lean_exe semr_mutant_eval where
  root := `SemRMutantMain

-- Existing enum tag/read/widen semantics and declaration-derived controls.
lean_lib SemREnumDiscriminant where
lean_lib SemREnumDiscriminantCheck where
lean_lib SemREnumDiscriminantAxiomAudit where

-- Complete-byte construction of the actual scalar Exit model; no source grade.
lean_lib MiniRustU64ProgramFromBytes where
lean_lib MiniRustU64ProgramFromBytesControls where

-- Original-node step proof for pending direct Boolean body derivations.
lean_lib SemRBoolBody where

lean_lib SemRBoolWholeBody where

lean_lib SemRBoolBodyChecker where

-- Equations composing the original decoder and the complete-byte root goal.
lean_lib SemRByteBinding where

lean_lib SemRDecodeCertificate where

lean_lib SemRDecodeCertificateCheck where

lean_lib SemRParserCertificate where

lean_lib SemRParserCertificateCheck where

-- Canonical integer assignment/substitution rules used by native WP consumers.
lean_lib SemRUnsignedSelect where

lean_lib SemRUnsignedSelectCheck where

lean_lib SemRUnsignedSelectAxiomAudit where
